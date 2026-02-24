# ALL-SAT SOLVER
# CREATES BDD FOR ALL P variables without combinatorial explosion
# ALL Q calculates from CUBE(P) like 2-CNF from |Q|
from dd.autoref import BDD
import gc
import sys
import os
import tracemalloc
from collections import defaultdict
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaSolver:
    def __init__(self):
        self.bdd = None
        self.clauses = []
        self.n = 0
        self.levels = []  # список уровней: [ (P0, Q0, bridges0), (P1, Q1, bridges1), ... ]
        self.peak_size = 0
        self.peak_memory = 0
        tracemalloc.start()
    
    def _print_memory(self, label):
        current, peak = tracemalloc.get_traced_memory()
        self.peak_memory = max(self.peak_memory, peak)
        print(f"  💾 {label}: {current/1024/1024:.1f} MB (пик {peak/1024/1024:.1f} MB)")
    
    def _find_vertex_cover_for_subset(self, var_subset):
        """Жадное вершинное покрытие для подмножества переменных"""
        if len(var_subset) <= 1:
            return [], list(var_subset)
        
        var_set = set(var_subset)
        edges = set()
        
        for clause in self.clauses:
            vars_in_clause = [abs(lit) for lit in clause if abs(lit) in var_set]
            if len(vars_in_clause) < 2:
                continue
            for i in range(len(vars_in_clause)):
                for j in range(i+1, len(vars_in_clause)):
                    a, b = sorted([vars_in_clause[i], vars_in_clause[j]])
                    edges.add((a, b))
        
        if not edges:
            return [], list(var_subset)
        
        degree = defaultdict(int)
        for a, b in edges:
            degree[a] += 1
            degree[b] += 1
        
        cover = set()
        uncovered = edges.copy()
        
        while uncovered and degree:
            max_vertex = max(degree.items(), key=lambda x: x[1])[0]
            cover.add(max_vertex)
            
            to_remove = []
            for edge in uncovered:
                if max_vertex in edge:
                    to_remove.append(edge)
                    a, b = edge
                    if a in degree:
                        degree[a] -= 1
                        if degree[a] == 0:
                            del degree[a]
                    if b in degree:
                        degree[b] -= 1
                        if degree[b] == 0:
                            del degree[b]
            for edge in to_remove:
                uncovered.remove(edge)
        
        P = list(cover)
        Q = [v for v in var_subset if v not in cover]
        return P, Q
    
    def _build_matryoshka(self):
        """Строит уровни матрешки P0 → P1 → P2 → ..."""
        print("🏗️ Построение матрешки...")
        levels = []
        current_vars = list(range(1, self.n + 1))
        depth = 0
        
        while current_vars and depth < 10:
            P, Q = self._find_vertex_cover_for_subset(current_vars)
            
            if not P:  # Не удалось найти покрытие
                levels.append({
                    'level': depth,
                    'P': [],
                    'Q': current_vars,
                    'bridges': 0
                })
                break
            
            # Считаем мостовые клозы
            P_set = set(P)
            Q_set = set(Q)
            bridges = 0
            for clause in self.clauses:
                vars_in_clause = set(abs(lit) for lit in clause)
                if vars_in_clause & P_set and vars_in_clause & Q_set:
                    bridges += 1
            
            levels.append({
                'level': depth,
                'P': P,
                'Q': Q,
                'bridges': bridges
            })
            
            print(f"  Уровень {depth}: |P|={len(P)}, |Q|={len(Q)}, мостов={bridges}")
            current_vars = P
            depth += 1
        
        self.levels = levels
        return levels
    
    def _get_clauses_for_vars(self, vars_set):
        """Возвращает клозы, где все переменные в vars_set"""
        result = []
        vars_set = set(vars_set)
        for clause in self.clauses:
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
    
    def solve(self, clauses, n):
        self.clauses = clauses
        self.n = n
        self.bdd = BDD()
        
        # Объявляем все переменные
        for i in range(1, n+1):
            self.bdd.declare(f'x{i}')
        
        # Включаем автоматическое переупорядочивание (совет Gemini)
        self.bdd.configure(reordering=True)
        
        # Шаг 1: Строим матрешку
        levels = self._build_matryoshka()
        
        if not levels:
            print("❌ Не удалось построить матрешку")
            return False
        
        # Шаг 2: Идём снизу вверх
        print("\n🔄 Подъём по матрешке...")
        
        # Начинаем с самого глубокого уровня
        bottom_level = levels[-1]
        current_vars = bottom_level['P'] if bottom_level['P'] else bottom_level['Q']
        print(f"\n🎯 Дно: |P|={len(current_vars)}")
        
        # Строим BDD для дна
        current_bdd = self.bdd.true
        bottom_clauses = self._get_clauses_for_vars(current_vars)
        for clause in bottom_clauses:
            current_bdd &= self._clause_to_bdd(clause)
        
        self.peak_size = max(self.peak_size, len(self.bdd))
        self._print_memory("после дна")
        
        # Поднимаемся вверх
        for i in range(len(levels)-2, -1, -1):
            level = levels[i]
            next_level = levels[i+1]
            
            print(f"\n📦 Уровень {i}: |P|={len(level['P'])}, |Q|={len(level['Q'])}")
            
            # Добавляем переменные текущего уровня (разница между P_i и P_{i+1})
            new_vars = set(level['P']) - set(next_level['P'])
            if new_vars:
                print(f"  Добавляем {len(new_vars)} новых переменных")
                
                # Добавляем клозы, ставшие полными на этом уровне
                all_vars_so_far = set(level['P']) | set(level['Q'])
                level_clauses = self._get_clauses_for_vars(all_vars_so_far)
                for clause in level_clauses:
                    current_bdd &= self._clause_to_bdd(clause)
            
            # Схлопываем Q этого уровня
            if level['Q']:
                q_vars = [f'x{q}' for q in level['Q']]
                print(f"  Схлопываем Q: {len(level['Q'])} переменных")
                current_bdd = self.bdd.exist(q_vars, current_bdd)
                
                # 🧹 Сборка мусора (совет Gemini)
                self.bdd.collect_garbage()
                
                # 🔄 Переупорядочивание раз в 3 уровня
                if i % 3 == 0:
                    self.bdd.configure(reordering=True)
            
            self.peak_size = max(self.peak_size, len(self.bdd))
            self._print_memory(f"после уровня {i}")
            
            if current_bdd == self.bdd.false:
                print("  ❌ UNSAT detected!")
                return False
            
            gc.collect()
        
        # Финальная проверка
        print("\n🔍 Финальная проверка...")
        if current_bdd == self.bdd.false:
            return False
        if current_bdd == self.bdd.true:
            return True
        
        solutions = self.bdd.pick_iter(current_bdd)
        try:
            next(solutions)
            return True
        except StopIteration:
            return False

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
    
    solver = MatryoshkaSolver()
    result = solver.solve(clauses, n)
    
    print(f"\n{'='*70}")
    print(f"🎯 Результат: {'SAT' if result else 'UNSAT'}")
    print(f"📊 Пиковый размер BDD: {solver.peak_size:,} узлов")
    print(f"💾 Пиковая память: {solver.peak_memory/1024/1024:.1f} MB")
    
    tracemalloc.stop()
