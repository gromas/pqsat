import random
import sys
import os
import time
from collections import deque
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaPuncherPower:
    def __init__(self, clauses):
        self.clauses = clauses
        self.triples = self._build_triples()
        self.K = len(self.triples)
        
        # Состояния храним как списки словарей {var: val}
        self.triple_states = [self._get_valid_states(t) for t in self.triples]
        
        # Битовые домены (Python int — нет ограничений!)
        self.initial_domains = [(1 << len(states)) - 1 for states in self.triple_states]
        
        # 1. Веса связей (Сила рычага)
        self.adj = [[] for _ in range(self.K)]
        self.impact_weights = [0] * self.K
        
        for i in range(self.K):
            # Собираем переменные i-й тройки
            vars_i = set()
            for clause in self.triples[i]:
                for lit in clause:
                    vars_i.add(abs(lit))
            
            for j in range(i + 1, self.K):
                # Собираем переменные j-й тройки
                vars_j = set()
                for clause in self.triples[j]:
                    for lit in clause:
                        vars_j.add(abs(lit))
                
                common = vars_i & vars_j
                if common:
                    weight = len(common)
                    self.adj[i].append((j, weight))
                    self.adj[j].append((i, weight))
                    self.impact_weights[i] += weight
                    self.impact_weights[j] += weight
        
        # 2. Предвычисленная совместимость (Матрица пробоя)
        self.compatibility = self._precompute_compatibility()

    def _build_triples(self):
        """Разбивает клозы на тройки (макро-узлы)"""
        used = [False] * len(self.clauses)
        triples = []
        
        for i in range(len(self.clauses)):
            if used[i]:
                continue
            
            # Начинаем с текущего клоза
            current = [self.clauses[i]]
            used[i] = True
            
            # Добавляем еще 2 клоза с максимальным пересечением
            for _ in range(2):
                best_idx = -1
                best_overlap = -1
                current_vars = set(abs(lit) for clause in current for lit in clause)
                
                for j in range(len(self.clauses)):
                    if not used[j]:
                        clause_vars = set(abs(lit) for lit in self.clauses[j])
                        overlap = len(current_vars & clause_vars)
                        if overlap > best_overlap:
                            best_overlap = overlap
                            best_idx = j
                
                if best_idx != -1:
                    current.append(self.clauses[best_idx])
                    used[best_idx] = True
            
            triples.append(current)
        
        return triples

    def _get_valid_states(self, triple_clauses):
        """Генерирует все допустимые состояния для тройки клозов"""
        vars_set = set()
        for clause in triple_clauses:
            for lit in clause:
                vars_set.add(abs(lit))
        
        vars_list = sorted(vars_set)
        n_vars = len(vars_list)
        valid = []
        
        for i in range(1 << n_vars):
            assignment = {vars_list[j]: (i >> j) & 1 for j in range(n_vars)}
            
            valid_triple = True
            for clause in triple_clauses:
                clause_satisfied = False
                for lit in clause:
                    var = abs(lit)
                    val = assignment[var]
                    if (lit > 0 and val == 1) or (lit < 0 and val == 0):
                        clause_satisfied = True
                        break
                if not clause_satisfied:
                    valid_triple = False
                    break
            
            if valid_triple:
                valid.append(assignment)
        
        return valid

    def _precompute_compatibility(self):
        """Предвычисляет матрицу совместимости между тройками"""
        compat = [{} for _ in range(self.K)]
        
        for t1 in range(self.K):
            # Собираем переменные t1
            vars1 = set()
            for clause in self.triples[t1]:
                for lit in clause:
                    vars1.add(abs(lit))
            
            for s1_idx, s1_map in enumerate(self.triple_states[t1]):
                compat[t1][s1_idx] = {}
                for t2, _ in self.adj[t1]:
                    # Собираем переменные t2
                    vars2 = set()
                    for clause in self.triples[t2]:
                        for lit in clause:
                            vars2.add(abs(lit))
                    
                    common_vars = vars1 & vars2
                    mask = 0
                    for s2_idx, s2_map in enumerate(self.triple_states[t2]):
                        if all(s1_map[v] == s2_map[v] for v in common_vars):
                            mask |= (1 << s2_idx)
                    compat[t1][s1_idx][t2] = mask
        
        return compat

    def ac3_filter(self, domains, start_node):
        """AC-3 фильтрация с битовыми масками"""
        queue = deque([start_node])
        in_queue = [False] * self.K
        in_queue[start_node] = True
        
        while queue:
            u = queue.popleft()
            in_queue[u] = False
            u_dom = domains[u]
            
            for v, _ in self.adj[u]:
                allowed_v = 0
                temp_u = u_dom
                idx = 0
                # Быстрый проход по активным битам
                while temp_u:
                    if temp_u & 1:
                        if idx in self.compatibility[u] and v in self.compatibility[u][idx]:
                            allowed_v |= self.compatibility[u][idx][v]
                    temp_u >>= 1
                    idx += 1
                
                if domains[v] & ~allowed_v:
                    domains[v] &= allowed_v
                    if not domains[v]:
                        return False
                    if not in_queue[v]:
                        queue.append(v)
                        in_queue[v] = True
        
        return True

    def select_lever_node(self, domains):
        """Эвристика "Рычаг": Мин. состояний + Макс. связность (Impact)"""
        best_node = -1
        best_score = float('inf')
        
        for i in range(self.K):
            d_size = bin(domains[i]).count('1')
            if d_size > 1:
                # Чем меньше состояний и больше связей, тем ниже score
                score = d_size / (self.impact_weights[i] + 1)
                if score < best_score:
                    best_score = score
                    best_node = i
        return best_node

    def random_walk_search(self, domains, depth=0):
        """Рекурсивный поиск с MRV, Random Walk и Impact-эвристикой"""
        target_node = self.select_lever_node(domains)
        if target_node == -1:
            return domains

        # Собираем доступные индексы состояний
        idx_list = []
        temp_dom = domains[target_node]
        max_states = len(self.triple_states[target_node])
        for i in range(max_states):
            if (temp_dom >> i) & 1:
                idx_list.append(i)
        
        random.shuffle(idx_list)

        for state_idx in idx_list:
            new_domains = list(domains)
            new_domains[target_node] = (1 << state_idx)
            
            if self.ac3_filter(new_domains, target_node):
                res = self.random_walk_search(new_domains, depth + 1)
                if res:
                    return res
        
        return None

    def _extract_solution(self, final_domains):
        """Извлекает полное решение из финальных доменов"""
        solution = {}
        for i in range(self.K):
            domain = final_domains[i]
            if domain == 0:
                continue
            # Находим индекс единственного установленного бита
            state_idx = (domain & -domain).bit_length() - 1
            solution.update(self.triple_states[i][state_idx])
        return solution

    def solve(self):
        """Основной метод решения"""
        start_time = time.time()
        
        print(f"📦 Троек: {self.K}")
        state_counts = [len(states) for states in self.triple_states]
        print(f"🧠 Состояний в тройках: min={min(state_counts)}, max={max(state_counts)}, ср={sum(state_counts)/len(state_counts):.1f}")
        print(f"🔄 Запуск AC-3 фильтрации...")
        
        # Начальная фильтрация
        domains = list(self.initial_domains)
        if not self.ac3_filter(domains, 0):
            print(f"❌ UNSAT на этапе препроцессинга")
            return None
        
        # Рекурсивный поиск
        result = self.random_walk_search(domains)
        end_time = time.time()
        
        if result:
            print(f"\n✅ SAT найден за {end_time - start_time:.2f} сек")
            solution = self._extract_solution(result)
            
            # Форматируем вывод как в DIMACS
            output = []
            for var in sorted(solution.keys()):
                output.append(f"{var if solution[var] else -var}")
            print(f"v {' '.join(map(str, output))} 0")
            
            return solution
        else:
            print(f"\n❌ UNSAT за {end_time - start_time:.2f} сек")
            return None


def main():
    if len(sys.argv) != 2:
        print("Использование: py rms.py <filename.cnf>")
        print("Пример: py rms.py benchmarks/uf50-01.cnf")
        sys.exit(1)
    
    filename = sys.argv[1]
    if not os.path.exists(filename):
        print(f"Ошибка: Файл '{filename}' не найден")
        sys.exit(1)
    
    # Загружаем через dimacs_loader
    print(f"\n📂 Загрузка: {filename}")
    n_vars, clauses = parse_dimacs_cnf(filename)
    
    print(f"📊 Статистика: {n_vars} переменных, {len(clauses)} клозов")
    
    # Создаём и запускаем решатель
    solver = MatryoshkaPuncherPower(clauses)
    solver.solve()


if __name__ == "__main__":
    main()
