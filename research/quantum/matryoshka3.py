from dd.autoref import BDD
import gc
import sys
import os
import time
import tracemalloc
from collections import defaultdict, Counter
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaLite:
    def __init__(self):
        self.bdd = None
        self.clauses = []
        self.n = 0
        self.last_seen = {}
        self.first_seen = {}
        self.var_lifetime = {}
        self.var_frequency = Counter()  # Частота появления переменных
        self.peak_memory = 0
        self.start_time = None
        tracemalloc.start()
    
    def _print_stats(self, label):
        current, peak = tracemalloc.get_traced_memory()
        self.peak_memory = max(self.peak_memory, peak)
        elapsed = time.time() - self.start_time
        print(f"  ⏱️ {elapsed:.1f}s | 💾 {current/1024/1024:.1f} MB | {label}")
    
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
        
        # Возвращаем информацию о типе задачи
        if len(long_lived) > len(self.clauses) * 0.3:  # >30% переменных - долгожители
            return "long_lived_dominant"
        return "normal"
    
    def _smart_clause_ordering(self, problem_type):
        """Умная сортировка клозов для минимизации активных переменных"""
        
        if problem_type == "long_lived_dominant":
            print("  🔥 Обнаружена задача с доминированием долгожителей - применяем специальную стратегию")
            return self._long_lived_strategy()
        else:
            return self._normal_strategy()
    
    def _long_lived_strategy(self):
        """Специальная стратегия для задач, где все переменные живут долго"""
        
        # Метрика: важность переменной = (частота * оставшаяся жизнь)
        var_importance = {}
        for var in range(1, self.n + 1):
            if var in self.last_seen:
                # Чем чаще встречается и чем дольше живет, тем важнее
                var_importance[var] = self.var_frequency[var] * (self.last_seen[var] - self.first_seen[var])
        
        # Сортируем клозы по убыванию суммарной важности переменных
        # Идея: сначала обрабатываем самые "связанные" клозы, чтобы BDD быстрее нашел структуру
        clause_scores = []
        for i, clause in enumerate(self.clauses):
            vars_in = [abs(lit) for lit in clause]
            
            # Суммарная важность переменных в клозе
            total_importance = sum(var_importance.get(v, 0) for v in vars_in)
            
            # Бонус за разнообразие переменных (чем больше разных, тем лучше для структуры)
            diversity_bonus = len(set(vars_in)) * 1000
            
            # Штраф за очень редкие переменные (их можно отложить)
            rarity_penalty = sum(1 for v in vars_in if self.var_frequency[v] < 5) * 500
            
            score = total_importance + diversity_bonus - rarity_penalty
            clause_scores.append(( -score, i, clause))  # По убыванию
        
        clause_scores.sort()
        
        # Альтернатива: перемешиваем с приоритетом важных
        sorted_clauses = [clause for _, _, clause in clause_scores]
        
        # Для долгожителей также пробуем кластеризацию по переменным
        # Берем топ-10 самых важных переменных
        top_vars = sorted(var_importance.items(), key=lambda x: x[1], reverse=True)[:10]
        top_var_ids = [v for v, _ in top_vars]
        
        print(f"  🔑 Топ-5 важных переменных: {top_var_ids[:5]}")
        
        return sorted_clauses
    
    def _normal_strategy(self):
        """Обычная стратегия для задач с короткоживущими переменными"""
        clause_scores = []
        
        for i, clause in enumerate(self.clauses):
            vars_in_clause = [abs(lit) for lit in clause]
            
            # Метрика 1: Есть ли переменная, которая умирает сразу после этого клоза?
            dying_here = sum(1 for v in vars_in_clause if self.last_seen[v] == i)
            
            # Метрика 2: Средняя оставшаяся жизнь переменных в клозе
            remaining_life = sum(self.last_seen[v] - i for v in vars_in_clause) / max(1, len(vars_in_clause))
            
            # Метрика 3: "Золотой" коэффициент
            gold_score = dying_here * 100 - remaining_life
            
            # Метрика 4: Приоритет для короткоживущих переменных
            short_term_bonus = sum(1 for v in vars_in_clause if self.var_lifetime[v] < 20) * 50
            
            total_score = gold_score + short_term_bonus
            clause_scores.append(( -total_score, i, clause))
        
        clause_scores.sort()
        return [clause for _, _, clause in clause_scores]
    
    def _clause_to_bdd(self, clause):
        b = self.bdd.false
        for lit in clause:
            name = f'x{abs(lit)}'
            if name not in self.bdd.vars:
                self.bdd.declare(name)
            lit_bdd = self.bdd.var(name) if lit > 0 else ~self.bdd.var(name)
            b |= lit_bdd
        return b
    
    def solve(self, clauses, n):
        self.start_time = time.time()
        self.clauses = list(clauses)
        self.n = n
        
        print(f"\n📊 {n} переменных, {len(clauses)} клозов")
        
        # Строим карты зависимостей и определяем тип задачи
        problem_type = self._build_dependency_map()
        self._print_stats("карты зависимостей построены")
        
        # Умная сортировка клозов
        self.clauses = self._smart_clause_ordering(problem_type)
        self._print_stats("клозы отсортированы")
        
        # Перестраиваем last_seen с учетом новой сортировки
        self.last_seen = {}
        for i, clause in enumerate(self.clauses):
            for lit in clause:
                self.last_seen[abs(lit)] = i
        
        # Инициализируем BDD
        self.bdd = BDD()
        
        # Пытаемся настроить реордеринг
        try:
            # Для долгожителей оставляем реордеринг включенным, но с большим порогом
            if problem_type == "long_lived_dominant":
                self.bdd.configure(reorder=True, max_memory=1024*1024*1024)
                print("  ✅ Реордеринг активен (необходимо для долгожителей)")
            else:
                self.bdd.configure(reorder=False)
                print("  ✅ Автоматический реордеринг отключен")
        except:
            print("  ⚠️ Не удалось настроить реордеринг")
        
        current_bdd = self.bdd.true
        eliminated_vars = set()
        
        # Для долгожителей делаем меньший прогрев
        warmup = 10 if problem_type == "long_lived_dominant" else 20
        print(f"\n🔥 Прогрев BDD (первые {warmup} клозов)...")
        
        # Фаза 1: Прогрев
        for i in range(min(warmup, len(self.clauses))):
            clause_bdd = self._clause_to_bdd(self.clauses[i])
            current_bdd &= clause_bdd
            
            if i % 5 == 0 or i == warmup-1:
                self._print_stats(f"прогрев {i+1}/{warmup}")
        
        self._print_stats("прогрев завершен")
        
        # Принудительная сборка мусора
        self.bdd.collect_garbage()
        gc.collect()
        
        # Фаза 2: Основной цикл
        print(f"\n🚀 Основной цикл с элиминацией...")
        
        # Для долгожителей используем динамический порог элиминации
        elimination_threshold = 5 if problem_type == "long_lived_dominant" else 1
        
        for i in range(warmup, len(self.clauses)):
            clause = self.clauses[i]
            
            # Добавляем клоз
            clause_bdd = self._clause_to_bdd(clause)
            current_bdd &= clause_bdd
            
            # Проверяем переменные на элиминацию
            vars_to_eliminate = set()
            for var in range(1, self.n + 1):
                if var in eliminated_vars:
                    continue
                if self.last_seen.get(var, -1) == i:
                    vars_to_eliminate.add(var)
            
            if vars_to_eliminate and len(vars_to_eliminate) >= elimination_threshold:
                # Элиминируем
                var_names = {f'x{var}' for var in vars_to_eliminate}
                current_bdd = self.bdd.exist(var_names, current_bdd)
                eliminated_vars.update(vars_to_eliminate)
                
                # Периодическая статистика
                if len(eliminated_vars) % 10 == 0:
                    self.bdd.collect_garbage()
                    self._print_stats(f"клоз {i+1}/{len(self.clauses)}, элиминировано {len(eliminated_vars)} пер.")
            
            # Проверка на UNSAT
            if current_bdd == self.bdd.false:
                print(f"  ❌ UNSAT на клозе {i+1}")
                return False
            
            # Периодическая сборка мусора
            if i % 50 == 0:
                gc.collect()
        
        # Финальная проверка
        self._print_stats("финал")
        
        if current_bdd == self.bdd.false:
            return False
        if current_bdd == self.bdd.true:
            return True
        
        # Ищем модель
        try:
            next(current_bdd.pick_iter(current_bdd))
            return True
        except StopIteration:
            return False
        finally:
            current, peak = tracemalloc.get_traced_memory()
            print(f"\n💾 Пик памяти: {peak/1024/1024:.1f} MB")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Использование: python matryoshka_solver_3.py <file.cnf>")
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
    tracemalloc.stop()
