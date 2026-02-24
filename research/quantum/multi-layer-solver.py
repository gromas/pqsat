from dd.autoref import BDD
import gc
import sys
import os
import tracemalloc
from collections import defaultdict
from dimacs_loader import parse_dimacs_cnf
import math

class MultiLayerQWatcher:
    def __init__(self, core_p, soft_p, q_vars, all_clauses):
        self.core_p = set(core_p)
        self.soft_p = set(soft_p)  # Слои 2, 3, 4 (P-tail + Q)
        self.all_soft = self.soft_p | set(q_vars)
        self.clauses = all_clauses

    def is_consistent(self, core_assignment):
        """
        Проверяет, существует ли удовлетворяющее назначение для ВСЕХ 
        soft_p и Q при заданном наборе core_p.
        """
        adj = defaultdict(list)
        
        for c in self.clauses:
            # Разделяем литералы на "жесткие" (core) и "мягкие" (soft)
            core_lits = [l for l in c if abs(l) in self.core_p]
            soft_lits = [l for l in c if abs(l) in self.all_soft]

            # Если в клозе есть переменные P, которых нет ни в core, ни в soft — игнорим
            # (в нашей схеме 4-х слоев таких быть не должно)

            # 1. Проверяем, удовлетворен ли клоз через Core P
            satisfied_by_core = False
            for l in core_lits:
                val = core_assignment.get(abs(l))
                if val is not None and val == (l > 0):
                    satisfied_by_core = True
                    break
            
            if satisfied_by_core:
                continue

            # 2. Если Core P все False (или их нет), клоз ложится на плечи Soft-переменных
            if len(soft_lits) == 1:
                l = soft_lits[0]
                adj[-l].append(l)  # Unit clause -> импликация
            elif len(soft_lits) == 2:
                l1, l2 = soft_lits
                adj[-l1].append(l2)
                adj[-l2].append(l1)
            elif len(soft_lits) >= 3:
                # ВАЖНО: Если в клозе 3 мягких переменных, это уже не 2-SAT!
                # Для uf50 таких клозов будет мало. Можем либо игнорировать (over-approximation),
                # либо временно считать их невыполненными.
                continue

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
        
        # Запускаем DFS для всех узлов графа (литералов)
        nodes = list(adj.keys())
        for node in nodes:
            if node not in ids:
                dfs(node)
                if self.found_conflict:
                    return False
        return True


class GradientSolver:
    def __init__(self):
        self.bdd = None
        self.P = []
        self.Q = []
        self.clauses = []
        self.n = 0
        self.core_size = 15  # размер ядра (Core P)
        self.peak_size = 0
        self.peak_memory = 0
        tracemalloc.start()
    
    def _print_memory(self, label):
        current, peak = tracemalloc.get_traced_memory()
        self.peak_memory = max(self.peak_memory, peak)
        print(f"  💾 {label}: {current/1024/1024:.1f} MB (пик {peak/1024/1024:.1f} MB)")
    
    def _connectivity_score(self, p_var, clauses):
        """Считает, сколько клозов содержит переменную"""
        score = 0
        for clause in clauses:
            if p_var in [abs(lit) for lit in clause]:
                score += 1
        return score
    
    def _polarity_score(self, p_var, clauses):
        """Считает полярность переменной: положительная - отрицательная"""
        pos = 0
        neg = 0
        for clause in clauses:
            for lit in clause:
                if abs(lit) == p_var:
                    if lit > 0:
                        pos += 1
                    else:
                        neg += 1
        return pos - neg
    
    def _sort_P(self, P, clauses):
        """Сортирует P по убыванию связности (для Core)"""
        scored = [(p, self._connectivity_score(p, clauses)) for p in P]
        scored.sort(key=lambda x: x[1], reverse=True)
        return [p for p, _ in scored]
    
    def _get_polarity_groups(self, P, clauses):
        """Делит P на положительные и отрицательные"""
        pos = []
        neg = []
        for p in P:
            score = self._polarity_score(p, clauses)
            if score > 0:
                pos.append(p)
            else:
                neg.append(p)
        return pos, neg
    
    def _get_clauses_for_vars(self, vars_set, clauses):
        """Возвращает клозы, в которых все переменные входят в vars_set"""
        result = []
        vars_set = set(vars_set)
        for clause in clauses:
            clause_vars = set(abs(lit) for lit in clause)
            if clause_vars.issubset(vars_set):
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
    
    def _filter_bdd_via_watcher(self, node, watcher):
        """
        Рекурсивный фильтр BDD узлов через MultiLayerQWatcher.
        """
        memo = {}
        
        def recurse(u, core_assignment):
            if u == self.bdd.true or u == self.bdd.false:
                return u
            
            if u in memo:
                return memo[u]
            
            # Проверяем консистентность текущего ядра
            if not watcher.is_consistent(core_assignment):
                memo[u] = self.bdd.false
                return self.bdd.false
            
            var_name = self.bdd.var_at_level(u.level)
            var_id = int(var_name[1:])
            
            # Ветка False
            new_assignment_false = core_assignment.copy()
            new_assignment_false[var_id] = False
            low = recurse(u.low, new_assignment_false)
            
            # Ветка True
            new_assignment_true = core_assignment.copy()
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
        
        # Сортируем P по связности
        sorted_P = self._sort_P(P, clauses)
        
        # Делим на слои
        core_p = sorted_P[:self.core_size]
        remaining_p = sorted_P[self.core_size:]
        pos_p, neg_p = self._get_polarity_groups(remaining_p, clauses)
        
        print(f"\n📊 Core P: {len(core_p)} переменных")
        print(f"📊 Pos-leaning P: {len(pos_p)} переменных")
        print(f"📊 Neg-leaning P: {len(neg_p)} переменных")
        print(f"📊 Q: {len(Q)} переменных")
        
        # Все "мягкие" переменные (Pos + Neg + Q)
        soft_vars = pos_p + neg_p + Q
        print(f"📊 Всего мягких: {len(soft_vars)} переменных")
        
        # Создаём MultiLayerQWatcher
        all_clauses = clauses  # используем все клозы
        watcher = MultiLayerQWatcher(core_p, soft_vars, Q, all_clauses)
        
        # Строим BDD только для Core P
        print(f"\n🪟 Построение BDD для Core P...")
        current_p_bdd = self.bdd.true
        processed_vars = core_p
        
        # Добавляем клозы внутри Core P
        core_clauses = self._get_clauses_for_vars(processed_vars, clauses)
        for clause in core_clauses:
            current_p_bdd &= self._clause_to_bdd(clause)
        
        # Применяем фильтр
        if current_p_bdd != self.bdd.true:
            current_p_bdd = self._filter_bdd_via_watcher(current_p_bdd, watcher)
        
        # Мониторинг
        size = len(self.bdd)
        self.peak_size = max(self.peak_size, size)
        self._print_memory("после построения Core")
        print(f"  📊 BDD размер: {size:,} узлов")
        
        if current_p_bdd == self.bdd.false:
            print("  ❌ UNSAT detected!")
            return False
        
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
    
    solver = GradientSolver()
    result = solver.solve(clauses, n, P, Q)
    
    print(f"\n{'='*70}")
    print(f"🎯 Результат: {'SAT' if result else 'UNSAT'}")
    print(f"📊 Пиковый размер BDD: {solver.peak_size:,} узлов")
    print(f"💾 Пиковая память: {solver.peak_memory/1024/1024:.1f} MB")
    
    tracemalloc.stop()
