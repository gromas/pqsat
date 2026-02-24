from dd.autoref import BDD
import gc
import sys
import os
import time
import tracemalloc
from collections import defaultdict, Counter
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaHybridV3:
    def __init__(self):
        self.bdd = None
        self.clauses = []
        self.n = 0
        self.levels = []
        self.last_seen = {}
        self.first_seen = {}
        self.var_lifetime = {}
        self.var_to_level = {}
        self.all_vars_declared = set()
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
    
    def _build_matryoshka_with_lifetime(self):
        """Строит матрешку с учетом времени жизни переменных"""
        print("\n🏗️ Построение гибридной матрешки...")
        
        # Строим карту last_seen
        self.last_seen = {}
        self.first_seen = {}
        for i, clause in enumerate(self.clauses):
            for lit in clause:
                var = abs(lit)
                if var not in self.first_seen:
                    self.first_seen[var] = i
                self.last_seen[var] = i
        
        # Вычисляем время жизни
        self.var_lifetime = {}
        for var in self.first_seen:
            self.var_lifetime[var] = self.last_seen[var] - self.first_seen[var]
        
        # Все переменные задачи
        all_vars = list(range(1, self.n + 1))
        
        # Разделяем переменные на "долгожителей" и "короткожителей"
        lifetime_threshold = len(self.clauses) * 0.3
        long_lived = [v for v in all_vars if self.var_lifetime.get(v, 0) > lifetime_threshold]
        short_lived = [v for v in all_vars if self.var_lifetime.get(v, 0) <= lifetime_threshold]
        
        print(f"  📊 Долгожители (>30% задачи): {len(long_lived)}")
        print(f"  📊 Короткожители: {len(short_lived)}")
        
        # Строим иерархию для долгожителей
        levels = []
        current_vars = long_lived
        depth = 0
        
        while current_vars and depth < 10:
            P, Q_level = self._find_vertex_cover_for_subset(current_vars)
            
            if not P:
                levels.append({
                    'level': depth,
                    'P': [],
                    'Q': current_vars,
                    'type': 'bottom'
                })
                break
            
            # Для каждой переменной в Q запоминаем уровень элиминации
            for var in Q_level:
                self.var_to_level[var] = depth
            
            levels.append({
                'level': depth,
                'P': P,
                'Q': Q_level,
                'type': 'hierarchical'
            })
            
            print(f"  Уровень {depth}: |P|={len(P)}, |Q|={len(Q_level)}")
            current_vars = P
            depth += 1
        
        # Добавляем короткожителей
        if short_lived:
            for var in short_lived:
                self.var_to_level[var] = depth
            levels.append({
                'level': depth,
                'P': [],
                'Q': short_lived,
                'type': 'streaming'
            })
            print(f"  Уровень {depth} (потоковый): |Q|={len(short_lived)}")
        
        self.levels = levels
        return levels
    
    def _declare_var_safe(self, var):
        """Безопасно объявляет переменную в BDD"""
        name = f'x{var}'
        if name not in self.all_vars_declared:
            if name not in self.bdd.vars:
                self.bdd.declare(name)
            self.all_vars_declared.add(name)
    
    def _clause_to_bdd(self, clause):
        """Превращает клоз в BDD"""
        clause_bdd = self.bdd.false
        for lit in clause:
            var = abs(lit)
            name = f'x{var}'
            # Убеждаемся, что переменная объявлена
            if name not in self.all_vars_declared:
                self._declare_var_safe(var)
            lit_bdd = self.bdd.var(name) if lit > 0 else ~self.bdd.var(name)
            clause_bdd |= lit_bdd
        return clause_bdd
    
    def _get_clauses_for_vars(self, vars_set):
        """Возвращает клозы, где все переменные в vars_set"""
        result = []
        vars_set = set(vars_set)
        for clause in self.clauses:
            clause_vars = set(abs(lit) for lit in clause)
            if clause_vars.issubset(vars_set):
                result.append(clause)
        return result
    
    def solve(self, clauses, n):
        self.start_time = time.time()
        self.clauses = list(clauses)
        self.n = n
        
        print(f"\n{'='*70}")
        print(f"МАТРЕШКА ГИБРИД V3 (2.0 + 3.0)")
        print(f"{'='*70}")
        print(f"📊 {n} переменных, {len(clauses)} клозов")
        
        # Шаг 1: Строим гибридную матрешку
        levels = self._build_matryoshka_with_lifetime()
        self._print_stats("матрешка построена")
        
        # Шаг 2: Инициализируем BDD
        self.bdd = BDD()
        self.all_vars_declared = set()
        
        # Пытаемся настроить реордеринг
        try:
            self.bdd.configure(reordering=True, max_memory=1024*1024*1024)
            print("  ✅ Реордеринг ВКЛЮЧЕН")
        except:
            print("  ⚠️ Не удалось настроить реордеринг")
        
        # Шаг 3: Проходим по уровням снизу вверх
        print("\n🔄 Подъём по матрешке...")
        
        # Начинаем с самого глубокого уровня
        bottom_level = levels[-1]
        current_vars = set(bottom_level['P'] if bottom_level['P'] else bottom_level['Q'])
        
        # Объявляем все переменные нижнего уровня
        print(f"\n🎯 Дно: {len(current_vars)} переменных")
        for var in current_vars:
            self._declare_var_safe(var)
        
        # Строим BDD для нижнего уровня
        current_bdd = self.bdd.true
        bottom_clauses = self._get_clauses_for_vars(current_vars)
        for clause in bottom_clauses:
            current_bdd &= self._clause_to_bdd(clause)
        
        self._print_stats(f"дно (ур.{len(levels)-1})")
        
        # Поднимаемся вверх
        for level_idx in range(len(levels)-2, -1, -1):
            level = levels[level_idx]
            
            print(f"\n📦 Уровень {level_idx} (тип: {level.get('type', 'hierarchical')})")
            
            if level.get('type') != 'streaming':
                # ИЕРАРХИЧЕСКИЙ УРОВЕНЬ
                new_vars = set(level['P']) - current_vars
                if new_vars:
                    print(f"  ➕ Добавляем P: {len(new_vars)} переменных")
                    for var in new_vars:
                        self._declare_var_safe(var)
                    
                    # Добавляем все клозы этого уровня
                    all_vars_here = set(level['P']) | set(level['Q'])
                    level_clauses = self._get_clauses_for_vars(all_vars_here)
                    
                    # Фильтруем только новые клозы
                    for clause in level_clauses:
                        clause_vars = set(abs(lit) for lit in clause)
                        # Добавляем только если есть переменные из нового уровня
                        if clause_vars & new_vars:
                            current_bdd &= self._clause_to_bdd(clause)
                    
                    current_vars = set(level['P'])  # Обновляем текущие переменные
                
                # Схлопываем Q (элиминируем)
                if level['Q']:
                    print(f"  🔄 Схлопываем Q: {len(level['Q'])} переменных")
                    q_vars = [f'x{q}' for q in level['Q']]
                    
                    # ВАЖНО: Проверяем, что все переменные существуют
                    existing_q_vars = [v for v in q_vars if v in self.all_vars_declared]
                    if existing_q_vars:
                        current_bdd = self.bdd.exist(existing_q_vars, current_bdd)
                        
                        # Удаляем из отслеживания
                        for var in level['Q']:
                            self.all_vars_declared.discard(f'x{var}')
                        
                        self.bdd.collect_garbage()
            
            else:
                # ПОТОКОВЫЙ УРОВЕНЬ
                print(f"  🌊 Потоковая обработка {len(level['Q'])} переменных")
                
                # Объявляем все переменные потокового уровня
                for var in level['Q']:
                    self._declare_var_safe(var)
                
                # Проходим по всем клозам
                eliminated_here = set()
                active_vars = set(level['Q'])
                
                for i, clause in enumerate(self.clauses):
                    # Добавляем клоз, если он содержит активные переменные
                    vars_in_clause = set(abs(lit) for lit in clause)
                    relevant_vars = vars_in_clause & active_vars
                    
                    if relevant_vars:
                        current_bdd &= self._clause_to_bdd(clause)
                    
                    # Ранняя элиминация
                    for var in list(active_vars):
                        if var in eliminated_here:
                            continue
                        if self.last_seen.get(var, -1) == i:
                            # Элиминируем переменную
                            current_bdd = self.bdd.exist({f'x{var}'}, current_bdd)
                            eliminated_here.add(var)
                            active_vars.remove(var)
                            self.all_vars_declared.discard(f'x{var}')
                            print(f"    ⚡ Ранняя элиминация x{var} на клозе {i}")
                    
                    # Периодическая сборка мусора
                    if i % 100 == 0:
                        self.bdd.collect_garbage()
                    
                    # Проверка на UNSAT
                    if current_bdd == self.bdd.false:
                        print(f"  ❌ UNSAT на клозе {i}")
                        return False
                
                print(f"  ✅ Элиминировано {len(eliminated_here)} переменных")
            
            self._print_stats(f"после ур.{level_idx}")
            
            if current_bdd == self.bdd.false:
                return False
            
            gc.collect()
        
        # Финальная проверка
        print("\n🔍 Финальная проверка...")
        self._print_stats("финал")
        
        if current_bdd == self.bdd.false:
            return False
        if current_bdd == self.bdd.true:
            return True
        
        # ИСПРАВЛЕНО: Используем bdd.pick_iter(), а не current_bdd.pick_iter()
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
            tracemalloc.stop()

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Использование: python matryoshka_hybrid_v3.py <file.cnf>")
        sys.exit(1)
    
    filename = sys.argv[1]
    if not os.path.exists(filename):
        print(f"Ошибка: Файл '{filename}' не найден")
        sys.exit(1)
    
    n, clauses = parse_dimacs_cnf(filename)
    solver = MatryoshkaHybridV3()
    result = solver.solve(clauses, n)
    
    print(f"\n{'='*70}")
    print(f"🎯 РЕЗУЛЬТАТ: {'SAT' if result else 'UNSAT'}")
