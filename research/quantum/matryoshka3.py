from dd.autoref import BDD
import gc
import sys
import os
import time
import tracemalloc
from collections import defaultdict, Counter
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaStreamV3:
    def __init__(self):
        self.bdd = None
        self.clauses = []
        self.n = 0
        self.last_seen = {}  # Карта последнего вхождения переменной
        self.first_seen = {}  # Карта первого вхождения
        self.var_lifetime = {}  # Длительность жизни
        self.var_frequency = Counter()  # Частота появления
        self.elimination_order = []  # Порядок элиминации переменных
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
    
    def _build_dependency_map(self):
        """Строит карты первого и последнего вхождения для каждой переменной"""
        self.first_seen = {}
        self.last_seen = {}
        self.var_frequency = Counter()
        
        for i, clause in enumerate(self.clauses):
            for lit in clause:
                var = abs(lit)
                self.var_frequency[var] += 1
                if var not in self.first_seen:
                    self.first_seen[var] = i
                self.last_seen[var] = i
        
        # Вычисляем длительность жизни
        self.var_lifetime = {}
        for var in self.first_seen:
            self.var_lifetime[var] = self.last_seen[var] - self.first_seen[var]
        
        # Анализируем статистику
        short_lived = [v for v, lt in self.var_lifetime.items() if lt < 20]
        medium_lived = [v for v, lt in self.var_lifetime.items() if 20 <= lt <= 100]
        long_lived = [v for v, lt in self.var_lifetime.items() if lt > 100]
        
        print(f"  📊 Короткоживущие (<20 клозов): {len(short_lived)}")
        print(f"  📊 Среднеживущие (20-100): {len(medium_lived)}")
        print(f"  📊 Долгоживущие (>100 клозов): {len(long_lived)}")
        
        # Строим порядок элиминации
        self.elimination_order = sorted(
            [(var, self.last_seen[var]) for var in range(1, self.n + 1) if var in self.last_seen],
            key=lambda x: x[1]  # Сортируем по времени последнего появления
        )
        
        print(f"  📊 Первая переменная для элиминации: x{self.elimination_order[0][0]} на клозе {self.elimination_order[0][1]}")
        print(f"  📊 Последняя переменная для элиминации: x{self.elimination_order[-1][0]} на клозе {self.elimination_order[-1][1]}")
        
        # Определяем тип задачи
        if len(long_lived) > self.n * 0.3:
            return "long_lived_dominant"
        return "normal"
    
    def _min_fill_ordering(self):
        """Min-fill эвристика для сортировки клозов"""
        print("\n🔄 Применяем Min-fill эвристику...")
        
        # Создаем граф переменных
        var_graph = defaultdict(set)
        for clause in self.clauses:
            vars_in = [abs(lit) for lit in clause]
            for i in range(len(vars_in)):
                for j in range(i+1, len(vars_in)):
                    var_graph[vars_in[i]].add(vars_in[j])
                    var_graph[vars_in[j]].add(vars_in[i])
        
        # Оцениваем каждый клоз
        clause_scores = []
        for i, clause in enumerate(self.clauses):
            vars_in = [abs(lit) for lit in clause]
            
            # Метрика 1: fill - сколько новых связей создаст этот клоз
            fill = 0
            for j, v1 in enumerate(vars_in):
                for v2 in vars_in[j+1:]:
                    if v2 not in var_graph[v1]:
                        fill += 1
            
            # Метрика 2: близость к элиминации
            elimination_proximity = min(self.last_seen[v] - i for v in vars_in)
            
            # Метрика 3: разнообразие переменных
            diversity = len(set(vars_in))
            
            # Итоговая оценка (чем меньше, тем лучше)
            score = fill * 10 - elimination_proximity * 5 - diversity * 3
            clause_scores.append((score, i, clause))
        
        # Сортируем
        clause_scores.sort()
        sorted_clauses = [clause for _, _, clause in clause_scores]
        
        print(f"  ✅ Первые 5 клозов после сортировки:")
        for i in range(min(5, len(sorted_clauses))):
            vars_in = [abs(lit) for lit in sorted_clauses[i]]
            lifetimes = [self.var_lifetime[v] for v in vars_in]
            elim_times = [self.last_seen[v] for v in vars_in]
            print(f"    Клоз {i}: vars={vars_in}, elim={elim_times}")
        
        return sorted_clauses
    
    def _clause_to_bdd(self, clause):
        """Превращает клоз в BDD"""
        clause_bdd = self.bdd.false
        for lit in clause:
            var_name = f'x{abs(lit)}'
            if var_name not in self.bdd.vars:
                self.bdd.declare(var_name)
            lit_bdd = self.bdd.var(var_name) if lit > 0 else ~self.bdd.var(var_name)
            clause_bdd |= lit_bdd
        return clause_bdd
    
    def solve(self, clauses, n):
        self.start_time = time.time()
        self.clauses = list(clauses)
        self.n = n
        
        print(f"\n{'='*70}")
        print(f"МАТРЕШКА STREAM V3")
        print(f"{'='*70}")
        print(f"📊 {n} переменных, {len(clauses)} клозов")
        
        # Шаг 1: Строим карту зависимостей
        problem_type = self._build_dependency_map()
        self._print_stats("карта зависимостей")
        
        # Шаг 2: Min-fill сортировка клозов
        self.clauses = self._min_fill_ordering()
        self._print_stats("после сортировки")
        
        # Перестраиваем last_seen с учетом новой сортировки
        self.last_seen = {}
        for i, clause in enumerate(self.clauses):
            for lit in clause:
                self.last_seen[abs(lit)] = i
        
        # Шаг 3: Инициализируем BDD
        print("\n🚀 Инициализация BDD...")
        self.bdd = BDD()
        
        # Настраиваем реордеринг в зависимости от типа задачи
        try:
            if problem_type == "long_lived_dominant":
                # Для долгожителей нужен реордеринг
                self.bdd.configure(reordering=True, max_memory=1024*1024*1024)
                print("  ✅ Реордеринг ВКЛЮЧЕН (режим долгожителей)")
            else:
                # Для короткоживущих можно отключить
                self.bdd.configure(reordering=False)
                print("  ✅ Реордеринг ОТКЛЮЧЕН")
        except:
            print("  ⚠️ Не удалось настроить реордеринг")
        
        current_bdd = self.bdd.true
        eliminated_vars = set()
        
        # Шаг 4: Потоковая обработка с ранней элиминацией
        print(f"\n📦 Потоковая обработка {len(self.clauses)} клозов...")
        
        for i, clause in enumerate(self.clauses):
            # Добавляем текущий клоз
            clause_bdd = self._clause_to_bdd(clause)
            current_bdd &= clause_bdd
            
            # Проверка на UNSAT
            if current_bdd == self.bdd.false:
                print(f"\n  ❌ UNSAT на клозе {i+1}")
                return False
            
            # Ранняя элиминация: находим переменные, которые больше не встретятся
            vars_to_eliminate = set()
            for var in range(1, self.n + 1):
                if var in eliminated_vars:
                    continue
                if self.last_seen.get(var, -1) == i:
                    vars_to_eliminate.add(var)
            
            if vars_to_eliminate:
                # Элиминируем все переменные сразу
                var_names = {f'x{var}' for var in vars_to_eliminate}
                current_bdd = self.bdd.exist(var_names, current_bdd)
                eliminated_vars.update(vars_to_eliminate)
                
                # Статистика
                if len(eliminated_vars) % 10 == 0:
                    self._print_stats(f"клоз {i+1}/{len(self.clauses)} (элим. {len(eliminated_vars)})")
                    self.bdd.collect_garbage()
            
            # Периодическая сборка мусора
            if i % 100 == 0 and i > 0:
                gc.collect()
        
        # Шаг 5: Финальная проверка
        print("\n🔍 Финальная проверка...")
        self._print_stats("финал")
        
        if current_bdd == self.bdd.false:
            return False
        if current_bdd == self.bdd.true:
            return True
        
        # Пытаемся найти решение
        try:
            next(current_bdd.pick_iter(current_bdd))
            return True
        except StopIteration:
            return False
        finally:
            # Итоговая статистика
            elapsed = time.time() - self.start_time
            print(f"\n{'='*70}")
            print(f"📊 ИТОГОВАЯ СТАТИСТИКА")
            print(f"  ⏱️ Время: {elapsed:.1f}с")
            print(f"  💾 Пик памяти: {self.peak_memory/1024/1024:.1f} MB")
            print(f"  📊 Пик узлов BDD: {self.peak_nodes:,}")
            print(f"  🔄 Элиминировано переменных: {len(eliminated_vars)}")
            tracemalloc.stop()


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Использование: python matryoshka_stream_v3.py <file.cnf>")
        sys.exit(1)
    
    filename = sys.argv[1]
    if not os.path.exists(filename):
        print(f"Ошибка: Файл '{filename}' не найден")
        sys.exit(1)
    
    n, clauses = parse_dimacs_cnf(filename)
    solver = MatryoshkaStreamV3()
    result = solver.solve(clauses, n)
    
    print(f"\n{'='*70}")
    print(f"🎯 РЕЗУЛЬТАТ: {'SAT' if result else 'UNSAT'}")
