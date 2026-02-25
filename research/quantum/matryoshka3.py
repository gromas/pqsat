from dd.autoref import BDD
import gc
import sys
import os
import time
import tracemalloc
from collections import defaultdict
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaV31:
    def __init__(self):
        self.bdd = None
        self.original_clauses = []  # Исходные клозы (для построения уровней)
        self.processed_clauses = []  # Отсортированные клозы для обработки
        self.n = 0
        self.levels = []
        self.last_seen = {}  # Будет построена после сортировки!
        self.var_to_level = {}
        self.peak_memory = 0
        self.peak_nodes = 0
        self.start_time = None
        tracemalloc.start()
    
    def _print_stats(self, label):
        current, peak = tracemalloc.get_traced_memory()
        self.peak_memory = max(self.peak_memory, peak)
        self.peak_nodes = max(self.peak_nodes, len(self.bdd) if self.bdd else 0)
        elapsed = time.time() - self.start_time
        print(f"  ⏱️ {elapsed:.1f}s | 💾 {current/1024/1024:.1f} MB | 📊 {len(self.bdd) if self.bdd else 0:,} узлов | {label}")
    
    def _find_vertex_cover_for_subset(self, var_subset):
        """Жадное вершинное покрытие для подмножества переменных"""
        if len(var_subset) <= 1:
            return [], list(var_subset)
        
        var_set = set(var_subset)
        edges = set()
        
        # Используем оригинальные клозы для построения графа
        for clause in self.original_clauses:
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
    
    def _build_levels(self):
        """Строит уровни P0 -> P1 -> P2 ... используя оригинальные клозы"""
        print("\n🏗️ Построение уровней матрешки...")
        levels = []
        current_vars = list(range(1, self.n + 1))
        depth = 0
        
        while current_vars and depth < 15:
            P, Q = self._find_vertex_cover_for_subset(current_vars)
            
            if not P:
                levels.append({
                    'level': depth,
                    'P': [],
                    'Q': current_vars
                })
                break
            
            levels.append({
                'level': depth,
                'P': P,
                'Q': Q
            })
            
            print(f"  Уровень {depth}: |P|={len(P)}, |Q|={len(Q)}")
            
            # Запоминаем уровень для каждой переменной из Q
            for var in Q:
                self.var_to_level[var] = depth
            
            current_vars = P
            depth += 1
        
        self.levels = levels
        return levels
    
    def _sort_clauses_by_level(self):
        """Сортирует клозы по уровню (от глубоких к поверхностным)"""
        
        # Определяем уровень каждого клоза
        clause_levels = []
        for clause in self.original_clauses:
            vars_in_clause = set(abs(lit) for lit in clause)
            
            # Уровень клоза = минимальный уровень среди его переменных
            min_level = float('inf')
            for var in vars_in_clause:
                level = self.var_to_level.get(var, len(self.levels))
                min_level = min(min_level, level)
            
            clause_levels.append((min_level, clause))
        
        # Сортируем: сначала глубокие уровни (меньший номер)
        clause_levels.sort(key=lambda x: x[0])
        
        # Выводим статистику
        print("\n📊 Распределение клозов по уровням:")
        level_counts = defaultdict(int)
        for level, _ in clause_levels:
            level_counts[level] += 1
        
        for level in sorted(level_counts.keys()):
            print(f"  Уровень {level}: {level_counts[level]} клозов")
        
        return [clause for _, clause in clause_levels]
    
    def _build_last_seen_after_sort(self):
        """Строит карту last_seen ПОСЛЕ сортировки клозов"""
        self.last_seen = {}
        for i, clause in enumerate(self.processed_clauses):
            for lit in clause:
                var = abs(lit)
                # Важно: перезаписываем - последнее вхождение в новом порядке
                self.last_seen[var] = i
        
        # Статистика
        print("\n📊 Порядок элиминации после сортировки:")
        elimination_order = sorted(self.last_seen.items(), key=lambda x: x[1])
        for var, pos in elimination_order[:10]:  # Первые 10
            print(f"  Переменная x{var} умрёт на клозе {pos}")
        if len(elimination_order) > 10:
            print(f"  ... и ещё {len(elimination_order)-10} переменных")
    
    def _clause_to_bdd(self, clause):
        """Превращает клоз в BDD"""
        clause_bdd = self.bdd.false
        for lit in clause:
            name = f'x{abs(lit)}'
            if name not in self.bdd.vars:
                self.bdd.declare(name)
            lit_bdd = self.bdd.var(name) if lit > 0 else ~self.bdd.var(name)
            clause_bdd |= lit_bdd
        return clause_bdd
    
    def solve(self, clauses, n):
        self.start_time = time.time()
        self.original_clauses = list(clauses)
        self.n = n
        
        print(f"\n{'='*70}")
        print(f"МАТРЕШКА 3.1 (С ПРАВИЛЬНЫМ last_seen)")
        print(f"{'='*70}")
        print(f"📊 {n} переменных, {len(clauses)} клозов")
        
        # Шаг 1: Строим уровни матрешки (используя оригинальные клозы)
        self._build_levels()
        self._print_stats("уровни построены")
        
        # Шаг 2: Сортируем клозы по уровню
        self.processed_clauses = self._sort_clauses_by_level()
        self._print_stats("клозы отсортированы")
        
        # Шаг 3: Строим last_seen ПОСЛЕ сортировки (ключевой момент!)
        self._build_last_seen_after_sort()
        self._print_stats("last_seen построен")
        
        # Шаг 4: Инициализируем BDD
        self.bdd = BDD()
        
        # Настраиваем реордеринг
        try:
            self.bdd.configure(reordering=True)
            print("  ✅ Реордеринг ВКЛЮЧЕН")
        except Exception as e:
            print(f"  ⚠️ Не удалось настроить реордеринг: {e}")
        
        current_bdd = self.bdd.true
        eliminated = set()
        
        # Шаг 5: Потоковая обработка с ранней элиминацией
        print(f"\n🚀 Потоковая обработка {len(self.processed_clauses)} клозов...")
        
        for i, clause in enumerate(self.processed_clauses):
            # Добавляем клоз
            clause_bdd = self._clause_to_bdd(clause)
            print("add_close")
            current_bdd &= clause_bdd
            
            # Проверка на UNSAT
            if current_bdd == self.bdd.false:
                print(f"\n  ❌ UNSAT на клозе {i+1}")
                return False
            
            # Ранняя элиминация по last_seen (теперь правильно синхронизировано!)
            vars_to_eliminate = set()
            for lit in clause:
                var = abs(lit)
                # Проверяем: это последний клоз для переменной в НОВОМ порядке?
                if var not in eliminated and self.last_seen.get(var, -1) == i:
                    vars_to_eliminate.add(var)
            
            if vars_to_eliminate:
                # Элиминируем переменные
                var_names = {f'x{var}' for var in vars_to_eliminate}
                print(f"eliminate {var_names}")
                current_bdd = self.bdd.exist(var_names, current_bdd)
                eliminated.update(vars_to_eliminate)
                
                # Статистика
                if len(eliminated) % 10 == 0:
                    self._print_stats(f"клоз {i+1}/{len(self.processed_clauses)} (элим. {len(eliminated)})")
                    self.bdd.collect_garbage()
            
            # Периодическая сборка мусора
            if i % 100 == 0 and i > 0:
                gc.collect()
        
        # Финальная проверка
        print("\n🔍 Финальная проверка...")
        self._print_stats("финал")
        
        if current_bdd == self.bdd.false:
            return False
        if current_bdd == self.bdd.true:
            return True
        
        try:
            next(self.bdd.pick_iter(current_bdd))
            return True
        except StopIteration:
            return False
        finally:
            elapsed = time.time() - self.start_time
            print(f"\n{'='*70}")
            print(f"📊 ИТОГОВАЯ СТАТИСТИКА")
            print(f"  ⏱️ Время: {elapsed:.1f}с")
            print(f"  💾 Пик памяти: {self.peak_memory/1024/1024:.1f} MB")
            print(f"  📊 Пик узлов BDD: {self.peak_nodes:,}")
            print(f"  🔄 Элиминировано переменных: {len(eliminated)} из {self.n}")
            tracemalloc.stop()

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Использование: python matryoshka_v31.py <file.cnf>")
        sys.exit(1)
    
    filename = sys.argv[1]
    if not os.path.exists(filename):
        print(f"Ошибка: Файл '{filename}' не найден")
        sys.exit(1)
    
    n, clauses = parse_dimacs_cnf(filename)
    solver = MatryoshkaV31()
    result = solver.solve(clauses, n)
    
    print(f"\n{'='*70}")
    print(f"🎯 РЕЗУЛЬТАТ: {'SAT' if result else 'UNSAT'}")
