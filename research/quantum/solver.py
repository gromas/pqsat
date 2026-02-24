from dd.autoref import BDD
import gc
import sys
import os
import tracemalloc
from collections import defaultdict
from dimacs_loader import parse_dimacs_cnf
import math

class QWatcher:
    def __init__(self, Q_vars, bridge_clauses):
        self.Q = set(Q_vars)
        self.bridge_clauses = bridge_clauses
        # Храним клозы, сгруппированные по переменным P для быстрой активации
        self.p_to_clauses = defaultdict(list)
        for c in bridge_clauses:
            for lit in c:
                if abs(lit) not in self.Q:
                    self.p_to_clauses[abs(lit)].append(c)
    
    def is_consistent(self, p_assignment, processed_vars):
        """
        p_assignment: dict {var_id: bool}
        processed_vars: список переменных P, уже обработанных
        Проверяет 2-SAT выполнимость Q при заданных P.
        """
        adj = defaultdict(list)
        
        for c in self.bridge_clauses:
            q_lits = [l for l in c if abs(l) in self.Q]
            p_lits = [l for l in c if abs(l) not in self.Q]
            
            # 1. Проверяем, есть ли в клозе переменные P, которые мы еще не трогали
            future_p = [l for l in p_lits if abs(l) not in processed_vars]
            
            if future_p:
                continue  # Клоз "живой", он может быть удовлетворен в будущем. Игнорируем его.
            
            # 2. Если все P-переменные клоза уже обработаны:
            # Проверяем, все ли они False
            all_p_false = True
            for l in p_lits:
                var = abs(l)
                # Если переменная есть в assignment и её значение совпадает с литералом (True для положительного)
                if var in p_assignment:
                    if (l > 0 and p_assignment[var]) or (l < 0 and not p_assignment[var]):
                        all_p_false = False
                        break
                else:
                    # Переменная обработана, но её нет в assignment? Странно, но на всякий случай
                    all_p_false = False
                    break
            
            if not all_p_false:
                continue  # Клоз уже True за счёт P, он не давит на Q
            
            # 3. А вот теперь это ЖЕСТКОЕ ограничение на Q
            if len(q_lits) == 1:
                # Unit Clause: (q1) -> добавляем ребро (-q1 -> q1)
                q = q_lits[0]
                adj[-q].append(q)
            elif len(q_lits) == 2:
                # 2-SAT Clause: (q1 or q2) -> (-q1 -> q2, -q2 -> q1)
                q1, q2 = q_lits
                adj[-q1].append(q2)
                adj[-q2].append(q1)
            # Случай len(q_lits) == 3 невозможен, т.к. Q - независимое множество
        
        # 2. Алгоритм Тарьяна для поиска SCC
        return self._has_no_conflicts(adj)
    
    def _has_no_conflicts(self, adj):
        visited_stack = []
        on_stack = set()
        ids = {}
        low = {}
        self.counter = 0
        self.found_conflict = False
        
        def dfs(at):
            ids[at] = low[at] = self.counter
            self.counter += 1
            visited_stack.append(at)
            on_stack.add(at)
            
            for to in adj.get(at, []):
                if to not in ids:
                    dfs(to)
                if to in on_stack:
                    low[at] = min(low[at], low[to])
            
            if ids[at] == low[at]:
                scc = set()
                while visited_stack:
                    node = visited_stack.pop()
                    on_stack.remove(node)
                    scc.add(node)
                    # ГЛАВНАЯ ПРОВЕРКА: x и -x в одной компоненте?
                    if -node in scc:
                        self.found_conflict = True
                    if node == at:
                        break
        
        # Запускаем DFS для всех узлов графа (литералов Q)
        nodes = list(adj.keys())
        for node in nodes:
            if node not in ids:
                dfs(node)
                if self.found_conflict:
                    return False
        return True


class SlidingWindowSolver:
    def __init__(self):
        self.bdd = None
        self.P = []
        self.Q = []
        self.clauses = []
        self.n = 0
        self.window_size = 10  # уменьшили окно до 20
        self.peak_size = 0
        self.peak_memory = 0
        tracemalloc.start()
    
    def _print_memory(self, label):
        current, peak = tracemalloc.get_traced_memory()
        self.peak_memory = max(self.peak_memory, peak)
        print(f"  💾 {label}: {current/1024/1024:.1f} MB (пик {peak/1024/1024:.1f} MB)")
    
    def _connectivity_score(self, p_var, Q_vars, clauses):
        """Считает, сколько клозов связывает p с Q"""
        score = 0
        for clause in clauses:
            vars_in_clause = set(abs(lit) for lit in clause)
            if p_var in vars_in_clause:
                # Есть ли в клозе переменная из Q?
                for q in Q_vars:
                    if q in vars_in_clause:
                        score += 1
                        break
        return score
    
    def _sort_P_by_connectivity(self, P, Q, clauses):
        """Сортирует P по убыванию связности с Q"""
        scored = [(p, self._connectivity_score(p, Q, clauses)) for p in P]
        scored.sort(key=lambda x: x[1], reverse=True)
        return [p for p, _ in scored]
    
    def _get_clauses_for_vars(self, vars_set, clauses):
        """Возвращает клозы, в которых все переменные входят в vars_set"""
        result = []
        vars_set = set(vars_set)
        for clause in clauses:
            clause_vars = set(abs(lit) for lit in clause)
            if clause_vars.issubset(vars_set):
                result.append(clause)
        return result
    
    def _get_bridge_clauses(self, p_vars, Q_vars, clauses):
        """Возвращает клозы, связывающие P и Q"""
        result = []
        p_set = set(p_vars)
        q_set = set(Q_vars)
        
        for clause in clauses:
            clause_vars = set(abs(lit) for lit in clause)
            # Клоз должен содержать хотя бы одну переменную из P и одну из Q
            if clause_vars & p_set and clause_vars & q_set:
                result.append(clause)
        return result
    
    def _clause_to_bdd(self, clause):
        """Превращает клоз в BDD"""
        clause_bdd = self.bdd.false
        for lit in clause:
            var_name = f'x{abs(lit)}'
            lit_bdd = self.bdd.var(var_name) if lit > 0 else ~self.bdd.var(var_name)
            clause_bdd |= lit_bdd
        return clause_bdd
    
    def _filter_bdd_via_qwatcher(self, node, q_watcher, processed_vars):
        """
        Рекурсивный фильтр BDD узлов через SCC-проверку Q.
        """
        memo = {}
        
        # Множество переменных P, которые реально влияют на Q
        relevant_p_vars = set()
        for clause in q_watcher.bridge_clauses:
            for lit in clause:
                if abs(lit) not in q_watcher.Q:
                    relevant_p_vars.add(abs(lit))
        
        def recurse(u, assignment):
            if u == self.bdd.true or u == self.bdd.false:
                return u
            
            # Кэш по узлу (без полного assignment)
            if u in memo:
                return memo[u]
            
            # Проверяем консистентность текущего частичного назначения
            # Передаём только релевантные переменные
            filtered_assignment = {k: v for k, v in assignment.items() 
                                  if k in relevant_p_vars}
            if not q_watcher.is_consistent(filtered_assignment, processed_vars):
                memo[u] = self.bdd.false
                return self.bdd.false
            
            var_name = self.bdd.var_at_level(u.level)
            var_id = int(var_name[1:])
            
            # Ветка False
            new_assignment_false = assignment.copy()
            new_assignment_false[var_id] = False
            low = recurse(u.low, new_assignment_false)
            
            # Ветка True
            new_assignment_true = assignment.copy()
            new_assignment_true[var_id] = True
            high = recurse(u.high, new_assignment_true)
            
            # Создаём узел (ITE)
            if low is high:
                res = low
            else:
                res = self.bdd.ite(self.bdd.add_var(var_name), high, low)
            
            memo[u] = res
            return res
        
        return recurse(node, {})
    
    def solve(self, clauses, n, P, Q):
        self.clauses = clauses
        self.n = n
        self.bdd = BDD()
        
        # Объявляем все переменные
        for i in range(1, n+1):
            self.bdd.declare(f'x{i}')
        
        # Сортируем P по связности с Q
        self.P = self._sort_P_by_connectivity(P, Q, clauses)
        self.Q = Q
        
        print(f"\n📊 P: {len(self.P)} переменных, Q: {len(self.Q)} переменных")
        print(f"Топ-5 P по связности: {self.P[:5]}")
        
        # Собираем все мостовые клозы для QWatcher
        all_bridge_clauses = self._get_bridge_clauses(self.P, Q, clauses)
        
        # Убираем дубликаты
        unique_bridge = []
        seen = set()
        for c in all_bridge_clauses:
            c_tuple = tuple(sorted(c))
            if c_tuple not in seen:
                seen.add(c_tuple)
                unique_bridge.append(c)
        
        q_watcher = QWatcher(Q, unique_bridge) if unique_bridge else None
        
        # Текущее BDD для обработанных P
        current_p_bdd = self.bdd.true
        processed_vars = []
        
        # Скользящее окно
        for i in range(0, len(self.P), self.window_size):
            window = self.P[i:i+self.window_size]
            processed_vars.extend(window)
            
            print(f"\n🪟 Окно {i//self.window_size + 1}: {window}")
            
            # Добавляем клозы внутри окна (уже все накопленные processed_vars)
            window_clauses = self._get_clauses_for_vars(processed_vars, clauses)
            for clause in window_clauses:
                current_p_bdd &= self._clause_to_bdd(clause)
            
            # 🔥 ФИЛЬТРАЦИЯ ЧЕРЕЗ QWATCHER (пока отключена из-за рекурсии)
            if q_watcher and current_p_bdd != self.bdd.true:
                # Строим bridge_bdd из мостовых клозов
                bridge_bdd = self.bdd.true
                current_bridge = self._get_bridge_clauses(processed_vars, Q, clauses)
                for clause in current_bridge:
                    bridge_bdd &= self._clause_to_bdd(clause)
                
                # Элиминируем Q
                q_vars = [f'x{q}' for q in Q]
                exists_q = self.bdd.exist(q_vars, bridge_bdd)
                current_p_bdd &= exists_q
            
            # Мониторинг
            size = len(self.bdd)
            self.peak_size = max(self.peak_size, size)
            self._print_memory(f"после окна {i//self.window_size + 1}")
            print(f"  📊 BDD размер: {size:,} узлов")
            
            if current_p_bdd == self.bdd.false:
                print("  ❌ UNSAT detected!")
                return False
            
            # Очистка
            gc.collect()
        
        # Финальная проверка
        print("\n🔍 Финальная проверка...")
        if current_p_bdd == self.bdd.false:
            return False
        if current_p_bdd == self.bdd.true:
            return True
        
        # Проверяем, есть ли хоть одно решение
        solutions = self.bdd.pick_iter(current_p_bdd)
        try:
            next(solutions)
            return True
        except StopIteration:
            return False


def find_vertex_cover(clauses, n):
    """
    Простая эвристика для вершинного покрытия:
    Берём все переменные, сортируем по частоте появления,
    добавляем в покрытие, пока не покроем все рёбра.
    """
    # Строим граф
    edges = set()
    for clause in clauses:
        vars_in_clause = list(abs(lit) for lit in clause)
        for i in range(len(vars_in_clause)):
            for j in range(i+1, len(vars_in_clause)):
                a, b = sorted([vars_in_clause[i], vars_in_clause[j]])
                edges.add((a, b))
    
    # Считаем степени
    degree = {}
    for a, b in edges:
        degree[a] = degree.get(a, 0) + 1
        degree[b] = degree.get(b, 0) + 1
    
    # Жадное покрытие
    cover = set()
    uncovered = edges.copy()
    
    while uncovered:
        # Берём вершину с макс степенью среди оставшихся рёбер
        if not degree:
            break
        max_vertex = max(degree.items(), key=lambda x: x[1])[0]
        cover.add(max_vertex)
        
        # Убираем все рёбра, инцидентные этой вершине
        to_remove = []
        for edge in uncovered:
            if max_vertex in edge:
                to_remove.append(edge)
                a, b = edge
                if a in degree:
                    degree[a] = max(0, degree[a] - 1)
                    if degree[a] == 0:
                        del degree[a]
                if b in degree:
                    degree[b] = max(0, degree[b] - 1)
                    if degree[b] == 0:
                        del degree[b]
        for edge in to_remove:
            uncovered.remove(edge)
    
    P = list(cover)
    Q = [i for i in range(1, n+1) if i not in cover]
    
    return P, Q


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Использование: python solver.py <filename.cnf>")
        sys.exit(1)
    
    filename = sys.argv[1]
    if not os.path.exists(filename):
        print(f"Ошибка: Файл '{filename}' не найден")
        sys.exit(1)
    
    n, clauses = parse_dimacs_cnf(filename)
    print(f"\n📊 {n} переменных, {len(clauses)} клозов")
    
    # Находим вершинное покрытие
    P, Q = find_vertex_cover(clauses, n)
    print(f"\n🎯 Вершинное покрытие: |P|={len(P)}, |Q|={len(Q)}")
    
    solver = SlidingWindowSolver()
    result = solver.solve(clauses, n, P, Q)
    
    print(f"\n{'='*70}")
    print(f"🎯 Результат: {'SAT' if result else 'UNSAT'}")
    print(f"📊 Пиковый размер BDD: {solver.peak_size:,} узлов")
    print(f"💾 Пиковая память: {solver.peak_memory/1024/1024:.1f} MB")
    
    tracemalloc.stop()
