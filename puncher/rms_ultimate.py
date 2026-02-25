import random
import sys
import os
import time
from collections import deque
from dimacs_loader import parse_dimacs_cnf

class MatryoshkaPuncherUltimate:
    def __init__(self, clauses):
        self.clauses = clauses
        self.triples = self._build_triples()
        self.K = len(self.triples)
        
        # Генерация состояний (до 256+ за счет Python long int)
        self.triple_states = [self._get_valid_states(t) for t in self.triples]
        self.initial_domains = [(1 << len(states)) - 1 for states in self.triple_states]
        
        # 1. Силовой рычаг (Impact)
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
                    w = len(common)
                    self.adj[i].append((j, w))
                    self.adj[j].append((i, w))
                    self.impact_weights[i] += w
                    self.impact_weights[j] += w
        
        # 2. Битовая совместимость
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
        n = len(vars_list)
        valid = []
        
        for i in range(1 << n):
            assign = {vars_list[j]: (i >> j) & 1 for j in range(n)}
            
            valid_triple = True
            for clause in triple_clauses:
                clause_satisfied = False
                for lit in clause:
                    var = abs(lit)
                    val = assign[var]
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
        """Предвычисляет матрицу совместимости между тройками"""
        compat = [{} for _ in range(self.K)]
        
        for i in range(self.K):
            # Собираем переменные i-й тройки
            vars_i = set()
            for clause in self.triples[i]:
                for lit in clause:
                    vars_i.add(abs(lit))
            
            for s_idx, s_map in enumerate(self.triple_states[i]):
                compat[i][s_idx] = {}
                for j, _ in self.adj[i]:
                    # Собираем переменные j-й тройки
                    vars_j = set()
                    for clause in self.triples[j]:
                        for lit in clause:
                            vars_j.add(abs(lit))
                    
                    common = vars_i & vars_j
                    mask = 0
                    for s2_idx, s2_map in enumerate(self.triple_states[j]):
                        if all(s_map[v] == s2_map[v] for v in common):
                            mask |= (1 << s2_idx)
                    compat[i][s_idx][j] = mask
        
        return compat

    def ac3_filter(self, domains, start_node):
        queue = deque([start_node])
        in_queue = [0] * self.K
        in_queue[start_node] = 1
        
        # Важно: Улики должны содержать только зафиксированные на данный момент узлы (assigned)
        # Для простоты: инициализируем конфликты текущим узлом
        conflict_set = {start_node}
        
        while queue:
            u = queue.popleft()
            in_queue[u] = 0
            u_dom = domains[u]
            
            for v, _ in self.adj[u]:
                allowed_v = 0
                # Быстрый проход по битам
                temp_u, idx = u_dom, 0
                while temp_u:
                    if temp_u & 1:
                        # Если нет в словаре - значит все состояния разрешены (маска -1)
                        allowed_v |= self.compatibility[u][idx].get(v, -1)
                    temp_u >>= 1
                    idx += 1
                
                # Если фильтрация что-то меняет
                if (domains[v] & allowed_v) != domains[v]:
                    domains[v] &= allowed_v
                    conflict_set.add(u) # Добавляем виновника сужения
                    
                    if not domains[v]:
                        return False, conflict_set # Коллапс
                    
                    if not in_queue[v]:
                        queue.append(v)
                        in_queue[v] = 1
        return True, None

    def backjump_search(self, domains, level, assigned_nodes):
        # 1. Выбор рычага (Impact-Based MRV)
        target = -1
        min_score = float('inf')
        for i in range(self.K):
            if i not in assigned_nodes:
                c = bin(domains[i]).count('1')
                if c == 0: return None, {i} # Ошибка домена
                if c > 1:
                    score = c / (self.impact_weights[i] + 1)
                    if score < min_score:
                        min_score, target = score, i
        
        if target == -1: return domains, None # Все зафиксированы

        # 2. Рандомизированный перебор
        # Извлекаем индексы установленных бит
        states = []
        temp, idx = domains[target], 0
        while temp:
            if temp & 1: states.append(idx)
            temp >>= 1; idx += 1
        random.shuffle(states)
        
        # Сюда собираем всех виновников неудач на этом уровне
        level_conflict_set = {target} 

        for s_idx in states:
            new_doms = list(domains)
            new_doms[target] = (1 << s_idx)
            
            ok, c_set = self.ac3_filter(new_doms, target)
            if ok:
                res, deep_c = self.backjump_search(new_doms, level + 1, assigned_nodes | {target})
                if res: return res, None
                c_set = deep_c
            
            # Если виноват не ТЕКУЩИЙ узел, а кто-то ВЫШЕ по стеку - прыгаем
            if target not in c_set:
                return None, c_set
            
            level_conflict_set.update(c_set)

        # Если дошли до конца и не нашли SAT - передаем виновников наверх
        level_conflict_set.discard(target)
        if not level_conflict_set: # Страховка от пустого сета
             level_conflict_set = {random.choice(list(assigned_nodes))} if assigned_nodes else {0}
             
        return None, level_conflict_set

    def solve(self):
        """Основной метод решения"""
        start_time = time.time()
        
        print(f"📦 Троек: {self.K}")
        state_counts = [len(states) for states in self.triple_states]
        print(f"🧠 Состояний в тройках: min={min(state_counts)}, max={max(state_counts)}, ср={sum(state_counts)/len(state_counts):.1f}")
        print(f"🔄 Запуск предварительной фильтрации...")
        
        # Начальная фильтрация для очистки мусора
        doms = list(self.initial_domains)
        for i in range(self.K):
            ok, _ = self.ac3_filter(doms, i)
            if not ok:
                print(f"❌ UNSAT на этапе препроцессинга")
                return None
        
        print(f"🔄 Запуск CBJ-поиска...")
        result, _ = self.backjump_search(doms, set())
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

    def _extract_solution(self, doms):
        """Извлекает полное решение из финальных доменов"""
        sol = {}
        for i in range(self.K):
            idx = doms[i].bit_length() - 1
            sol.update(self.triple_states[i][idx])
        return sol


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
    solver = MatryoshkaPuncherUltimate(clauses)
    solver.solve()


if __name__ == "__main__":
    main()
