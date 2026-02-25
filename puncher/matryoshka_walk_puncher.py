import sys
import collections
import random
import time
from itertools import combinations

# Настройка рекурсии для глубоких деревьев uf100
sys.setrecursionlimit(100000)

def load_dimacs(file_path):
    clauses = []
    vars_count = 0
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', 'p', '%')) or line == '0': continue
            if line.startswith('p cnf'):
                vars_count = int(line.split()[2])
                continue
            parts = line.split()
            clause = [int(p) for p in parts if int(p) != 0]
            if clause: clauses.append(clause)
    return clauses, vars_count

def get_triplets(clauses):
    used = [False] * len(clauses)
    triplets = []
    for i in range(len(clauses)):
        if used[i]: continue
        curr = [clauses[i]]; used[i] = True
        for _ in range(2):
            best, m_o, c_vars = -1, -1, set(abs(x) for c in curr for x in c)
            for j in range(len(clauses)):
                if not used[j]:
                    o = len(c_vars & set(abs(x) for x in clauses[j]))
                    if o > m_o: m_o, best = o, j
            if best != -1: curr.append(clauses[best]); used[best] = True
        triplets.append(curr)
    return triplets

def get_valid_states(triplet):
    t_vars = sorted(list(set(abs(x) for c in triplet for x in c)))
    valid = []
    for i in range(2**len(t_vars)):
        at = {v: (i >> idx) & 1 for idx, v in enumerate(t_vars)}
        if all(any((l > 0 and at[abs(l)] == 1) or (l < 0 and at[abs(l)] == 0) for l in c) for c in triplet):
            valid.append(at)
    return valid, t_vars

def run_ac3(triplet_data, adj, initial_alive):
    alive = [s.copy() for s in initial_alive]
    queue = collections.deque([(i, j) for i in adj for j, _ in adj[i]])
    while queue:
        i, j = queue.popleft()
        common = next(c for n, c in adj[i] if n == j)
        to_remove = set()
        for idx_i in alive[i]:
            si_map = triplet_data[i][idx_i]
            supported = any(all(si_map[v] == triplet_data[j][idx_j][v] for v in common) for idx_j in alive[j])
            if not supported: to_remove.add(idx_i)
        if to_remove:
            alive[i] -= to_remove
            if not alive[i]: return None
            for k, _ in adj[i]:
                if k != j: queue.append((k, i))
    return alive

def solve_recursive(triplet_data, adj, current_alive, depth=0):
    # Проверка на SAT: если во всех тройках осталось ровно по 1 состоянию
    if all(len(s) == 1 for s in current_alive):
        return current_alive

    # Выбор "Рычага" (MRV эвристика: тройка с мин. кол-вом состояний > 1)
    options = [(i, len(s)) for i, s in enumerate(current_alive) if len(s) > 1]
    if not options: return current_alive
    
    # Сортируем по количеству состояний (жадный выбор)
    target_idx, _ = min(options, key=lambda x: x[1])
    
    # RANDOM WALK: Перемешиваем состояния выбранного рычага
    candidate_states = list(current_alive[target_idx])
    random.shuffle(candidate_states)
    
    for s_idx in candidate_states:
        # Branching
        branched = [s.copy() for s in current_alive]
        branched[target_idx] = {s_idx}
        
        # Лавина AC-3
        result = run_ac3(triplet_data, adj, branched)
        
        if result is not None:
            if depth < 5: # Лог только для верхних уровней
                print(f"{'  '*depth}Уровень {depth}: Тройка {target_idx}, состояние {s_idx} OK. Спуск...")
            
            res = solve_recursive(triplet_data, adj, result, depth + 1)
            if res is not None: return res
            
    return None

def main():
    if len(sys.argv) < 2:
        print("Usage: py matryoshka_random_puncher.py <file.cnf>"); return
    
    start_time = time.time()
    clauses, vars_total = load_dimacs(sys.argv[1])
    triplets = get_triplets(clauses)
    
    print(f"--- Рандомная Матрёшка: {sys.argv[1]} ---")
    print(f"Троек: {len(triplets)}")

    triplet_data, triplet_vars = [], []
    adj = collections.defaultdict(list)
    for i, t in enumerate(triplets):
        states, v_list = get_valid_states(t)
        triplet_data.append(states); triplet_vars.append(set(v_list))

    for i, j in combinations(range(len(triplets)), 2):
        common = triplet_vars[i] & triplet_vars[j]
        if common:
            adj[i].append((j, common)); adj[j].append((i, common))

    # Начальная фильтрация
    base_alive = [set(range(len(td))) for td in triplet_data]
    base_alive = run_ac3(triplet_data, adj, base_alive)
    
    if base_alive is None:
        print("UNSAT на этапе пре-процессинга."); return

    # Запуск рекурсивного поиска с Random Walk
    result = solve_recursive(triplet_data, adj, base_alive)

    if result:
        print(f"\n--- !!! НАЙДЕНО РЕШЕНИЕ (SAT) !!! ---")
        print(f"Время: {time.time() - start_time:.2f} сек.")
        # Сборка решения
        final_assignment = {}
        for i, s_set in enumerate(result):
            s_idx = list(s_set)[0]
            final_assignment.update(triplet_data[i][s_idx])
        
        res_str = " ".join([f"{v if val else -v}" for v, val in sorted(final_assignment.items())])
        print(f"v {res_str} 0")
    else:
        print(f"\n--- ИТОГ: UNSAT ---")
        print(f"Время: {time.time() - start_time:.2f} сек.")

if __name__ == "__main__":
    main()
