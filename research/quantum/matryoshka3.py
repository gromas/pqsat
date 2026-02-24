from dd.autoref import BDD
import gc
import sys
import os
import time
import tracemalloc
from collections import defaultdict
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaLite:
    def __init__(self):
        self.main_bdd = None
        self.clauses = []
        self.n = 0
        self.levels = []
        self.peak_memory = 0
        self.start_time = None
        tracemalloc.start()
    
    def _print_stats(self, label):
        current, peak = tracemalloc.get_traced_memory()
        self.peak_memory = max(self.peak_memory, peak)
        elapsed = time.time() - self.start_time
        print(f"  ⏱️ {elapsed:.1f}s | 💾 {current/1024/1024:.1f} MB | {label}")
    
    def _find_vertex_cover_for_subset(self, var_subset):
        if len(var_subset) <= 1:
            return [], list(var_subset)
        
        var_set = set(var_subset)
        edges = set()
        for clause in self.clauses:
            vars_in = [abs(lit) for lit in clause if abs(lit) in var_set]
            if len(vars_in) < 2:
                continue
            for i in range(len(vars_in)):
                for j in range(i+1, len(vars_in)):
                    a, b = sorted([vars_in[i], vars_in[j]])
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
            max_v = max(degree.items(), key=lambda x: x[1])[0]
            cover.add(max_v)
            to_remove = []
            for e in uncovered:
                if max_v in e:
                    to_remove.append(e)
                    a, b = e
                    degree[a] -= 1
                    degree[b] -= 1
                    if degree[a] == 0: del degree[a]
                    if degree[b] == 0: del degree[b]
            for e in to_remove:
                uncovered.remove(e)
        
        P = list(cover)
        Q = [v for v in var_subset if v not in cover]
        return P, Q
    
    def _build_plan(self):
        print("📋 Компиляция плана...")
        current = list(range(1, self.n + 1))
        level = 0
        while current and level < 10:
            P, Q = self._find_vertex_cover_for_subset(current)
            if not P:
                self.levels.append({'P': [], 'Q': current})
                break
            self.levels.append({'P': P, 'Q': Q})
            print(f"  Уровень {level}: |P|={len(P)}, |Q|={len(Q)}")
            current = P
            level += 1
        self.levels.reverse()  # теперь дно - индекс 0
        return self.levels
    
    def _get_clauses_for(self, vars_set):
        result = []
        vs = set(vars_set)
        for c in self.clauses:
            if set(abs(lit) for lit in c).issubset(vs):
                result.append(c)
        return result
    
    def _clause_to_bdd(self, bdd_mgr, clause):
        b = bdd_mgr.false
        for lit in clause:
            name = f'x{abs(lit)}'
            lit_bdd = bdd_mgr.var(name) if lit > 0 else ~bdd_mgr.var(name)
            b |= lit_bdd
        return b
    
    def solve(self, clauses, n):
        self.start_time = time.time()
        self.clauses = clauses
        self.n = n
        
        print(f"\n📊 {n} переменных, {len(clauses)} клозов")
        self._build_plan()
        
        # Основной BDD - только для самого глубокого уровня
        self.manager = BDD()
        bottom_vars = self.levels[0]['P']
        if not bottom_vars:
            bottom_vars = self.levels[0]['Q']
        for v in bottom_vars:
            self.manager.declare(f'x{v}')
        self.main_bdd = self.manager.true
        
        # Строим дно
        bottom_clauses = self._get_clauses_for(bottom_vars)
        for c in bottom_clauses:
            self.main_bdd &= self._clause_to_bdd(self.manager, c)
        self._print_stats("дно")
        
        # Поднимаемся по уровням
        for i in range(1, len(self.levels)):
            level = self.levels[i]
            next_level = self.levels[i-1]
            
            # Новые переменные этого уровня
            new_vars = set(level['P']) - set(next_level['P'])
            if not new_vars and not level['Q']:
                continue
            
            # 🔥 ЛОКАЛЬНЫЙ КОНТЕЙНЕР
            local_manager = BDD()
            local = local_manager.true
            all_vars_here = set(level['P']) | set(level['Q'])
            for v in all_vars_here:
                local_manager.declare(f'x{v}')
            
            # Строим локальный BDD для этого уровня
            level_clauses = self._get_clauses_for(all_vars_here)
            for c in level_clauses:
                local &= self._clause_to_bdd(local_manager, c)
            
            # ТОТАЛЬНАЯ ЗАЧИСТКА
            vars_to_keep = set(next_level['P'])
            vars_to_kill = all_vars_here - vars_to_keep
            
            if vars_to_kill:
                kill_set = {f'x{v}' for v in vars_to_kill}
                local = local_manager.exist(kill_set, local)
                local_manager.collect_garbage()
            
            # Перенос в основной BDD
            # Добавляем недостающие переменные
            for v in vars_to_keep:
                if f'x{v}' not in self.manager.vars:
                    self.manager.declare(f'x{v}')
            
            # Конъюнкция с локальным результатом
            # Это костыль - в идеале нужно копирование BDD между менеджерами
            # Но для теста сойдет
            temp = self.manager.true
            for assign in local_manager.pick_iter(local):
                # Строим BDD для этого присваивания
                assign_bdd = self.manager.true
                for var, val in assign.items():
                    if var.startswith('x'):
                        var_bdd = self.manager.var(var) if val else ~self.manager.var(var)
                        assign_bdd &= var_bdd
                temp &= assign_bdd
            
            self.main_bdd &= temp
            
            self._print_stats(f"уровень {i}")
            
            if self.main_bdd == self.manager.false:
                print("  ❌ UNSAT")
                return False
            
            gc.collect()
        
        # Финал
        if self.main_bdd == self.main_bdd.false:
            return False
        if self.main_bdd == self.main_bdd.true:
            return True
        try:
            next(self.main_bdd.pick_iter(self.main_bdd))
            return True
        except StopIteration:
            return False

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Использование: python matryoshka_lite.py <file.cnf>")
        sys.exit(1)
    
    filename = sys.argv[1]
    if not os.path.exists(filename):
        print(f"Ошибка: Файл '{filename}' не найден")
        sys.exit(1)
    
    n, clauses = parse_dimacs_cnf(filename)
    solver = MatryoshkaLite()
    result = solver.solve(clauses, n)
    
    print(f"\n{'='*70}")
    print(f"🎯 РЕЗУЛЬТАТ: {'SAT' if result else 'UNSAT'}")
    current, peak = tracemalloc.get_traced_memory()
    print(f"💾 Пик памяти: {peak/1024/1024:.1f} MB")
    tracemalloc.stop()
