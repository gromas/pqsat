import random
import sys
import os
import time
from collections import deque

# --- Загрузчик DIMACS ---
def parse_dimacs_cnf(filepath):
    clauses = []
    n = 0
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p'):
                parts = line.split()
                if len(parts) >= 3:
                    n = int(parts[2])
                continue
            try:
                nums = list(map(int, line.split()))
            except ValueError:
                continue
            if nums and nums[-1] == 0:
                nums = nums[:-1]
            if nums:
                clauses.append(nums)
    return n, clauses


# --- Основной класс стабильной версии ---
class MatryoshkaPuncherStable:
    def __init__(self, clauses):
        self.clauses = clauses
        self.triples = self._build_triples()
        self.K = len(self.triples)
        
        # Генерация состояний для каждой тройки
        self.triple_states = [self._get_valid_states(t) for t in self.triples]
        self.initial_domains = [(1 << len(states)) - 1 for states in self.triple_states]
        
        # Предвычисленная совместимость (плотные списки для скорости)
        self.adj = [[] for _ in range(self.K)]
        self.impact_weights = [0] * self.K
        
        # Предвычисляем переменные для каждой тройки
        self.triple_vars = []
        for t in self.triples:
            vars_set = set()
            for clause in t:
                for lit in clause:
                    vars_set.add(abs(lit))
            self.triple_vars.append(vars_set)
        
        for i in range(self.K):
            vars_i = self.triple_vars[i]
            for j in range(i + 1, self.K):
                common = vars_i & self.triple_vars[j]
                if common:
                    w = len(common)
                    self.adj[i].append(j)
                    self.adj[j].append(i)
                    self.impact_weights[i] += w
                    self.impact_weights[j] += w
        
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
                current_vars = set()
                for clause in current:
                    for lit in clause:
                        current_vars.add(abs(lit))
                
                for j in range(len(self.clauses)):
                    if not used[j]:
                        clause_vars = set()
                        for lit in self.clauses[j]:
                            clause_vars.add(abs(lit))
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
        # Собираем все переменные в тройке
        vars_set = set()
        for clause in triple_clauses:
            for lit in clause:
                vars_set.add(abs(lit))
        
        vars_list = sorted(vars_set)
        n = len(vars_list)
        valid = []
        
        for i in range(1 << n):
            assign = {vars_list[j]: (i >> j) & 1 for j in range(n)}
            
            # Проверяем, удовлетворяет ли назначение ВСЕМ клозам тройки
            valid_triple = True
            for clause in triple_clauses:
                clause_satisfied = False
                for lit in clause:
                    var = abs(lit)
                    val = assign.get(var)
                    if (lit > 0 and val == 1) or (lit < 0 and val == 0):
                        clause_satisfied = True
                        break
                if not clause_satisfied:
                    valid_triple = False
                    break
            
            if valid_triple:
                valid.append(assign)
        
        return valid

    def _precompute_compatibility(self):
        """Храним маски в плотных списках для исключения dict.get()"""
        compat = [[None] * self.K for _ in range(self.K)]
        
        for i in range(self.K):
            vars_i = self.triple_vars[i]
            for j in self.adj[i]:
                common = vars_i & self.triple_vars[j]
                masks = []
                for s_idx, s_map in enumerate(self.triple_states[i]):
                    m = 0
                    for s2_idx, s2_map in enumerate(self.triple_states[j]):
                        if all(s_map[v] == s2_map[v] for v in common):
                            m |= (1 << s2_idx)
                    masks.append(m)
                compat[i][j] = masks
        
        return compat

    def ac3_filter(self, domains, start_node):
        queue = deque([start_node])
        in_queue = [False] * self.K
        in_queue[start_node] = True
        
        while queue:
            u = queue.popleft()
            in_queue[u] = False
            u_dom = domains[u]
            
            # ОПТИМИЗАЦИЯ: Если в узле осталось 1 состояние, 
            # берем готовую маску из таблицы без циклов
            is_single = (u_dom & (u_dom - 1) == 0)
            if is_single:
                idx = u_dom.bit_length() - 1
                for v in self.adj[u]:
                    allowed_v = self.compatibility[u][v][idx]
                    if (domains[v] & allowed_v) != domains[v]:
                        domains[v] &= allowed_v
                        if not domains[v]: return False
                        if not in_queue[v]:
                            queue.append(v); in_queue[v] = True
            else:
                # Если состояний много, используем "быстрый пропуск" нулевых байтов
                for v in self.adj[u]:
                    allowed_v = 0
                    temp_u, idx = u_dom, 0
                    masks_u_v = self.compatibility[u][v]
                    # Python оптимизирует работу с большими int, 
                    # но мы поможем ему, пропуская пустые участки
                    while temp_u:
                        if temp_u & 0xff: # Проверяем сразу 8 состояний
                            for i in range(8):
                                if (temp_u >> i) & 1:
                                    allowed_v |= masks_u_v[idx + i]
                        temp_u >>= 8
                        idx += 8
                    
                    if (domains[v] & allowed_v) != domains[v]:
                        domains[v] &= allowed_v
                        if not domains[v]: return False
                        if not in_queue[v]:
                            queue.append(v); in_queue[v] = True
        return True
        
    def recursive_walk(self, domains, assigned):
        # Выбор рычага: ищем узел, где (Домен / Связи) минимален
        target, best_score = -1, float('inf')
        for i in range(self.K):
            if i not in assigned:
                c = bin(domains[i]).count('1')
                if c == 1: continue # Уже определен фильтром
                if c == 0: return None # Тупик
                
                # РЫЧАГ: Чем меньше состояний (c) и чем больше ВЕС связей, тем приоритетнее
                score = c / (self.impact_weights[i] + 2) 
                if score < best_score:
                    best_score, target = score, i
        
        if target == -1: 
            return domains # Все схлопнулось в SAT!

        # Перебор состояний (Random Walk)
        max_states = len(self.triple_states[target])
        states = [i for i in range(max_states) if (domains[target] >> i) & 1]
        random.shuffle(states)
        
        for s_idx in states:
            new_doms = list(domains)
            new_doms[target] = (1 << s_idx)
            
            if self.ac3_filter(new_doms, target):
                res = self.recursive_walk(new_doms, assigned | {target})
                if res:
                    return res
        
        return None

    def solve(self):
        """Основной метод решения"""
        start_time = time.time()
        
        print(f"📦 Троек: {self.K}")
        state_counts = [len(states) for states in self.triple_states]
        if state_counts:
            print(f"🧠 Состояний в тройках: min={min(state_counts)}, max={max(state_counts)}, ср={sum(state_counts)/len(state_counts):.1f}")
        
        print(f"🔄 Запуск AC-3 фильтрации...")
        
        # Начальная фильтрация
        doms = list(self.initial_domains)
        for i in range(self.K):
            if not self.ac3_filter(doms, i):
                print(f"❌ UNSAT на этапе препроцессинга")
                end_time = time.time()
                print(f"⏱️ Время: {end_time - start_time:.2f} сек")
                return None
        
        print(f"🔄 Запуск рекурсивного поиска...")
        result = self.recursive_walk(doms, set())
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

    def _extract_solution(self, final_domains):
        """Извлекает полное решение из финальных доменов"""
        solution = {}
        for i in range(self.K):
            idx = final_domains[i].bit_length() - 1
            if idx >= 0:
                solution.update(self.triple_states[i][idx])
        return solution


def main():
    if len(sys.argv) != 2:
        print("Использование: py rms_stable.py <filename.cnf>")
        print("Пример: py rms_stable.py benchmarks/uf50-01.cnf")
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
    solver = MatryoshkaPuncherStable(clauses)
    solver.solve()


if __name__ == "__main__":
    main()
