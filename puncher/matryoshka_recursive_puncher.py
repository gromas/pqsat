import sys
import collections
import time
from itertools import combinations
from dd.autoref import BDD

# Настройка лимитов для глубоких деревьев
sys.setrecursionlimit(100000)

def load_dimacs(file_path):
    clauses = []
    v_count = 0
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', 'p', '%')) or line == '0': continue
            if line.startswith('p cnf'):
                v_count = int(line.split()[2])
                continue
            parts = line.split()
            clause = [int(p) for p in parts if int(p) != 0]
            if clause: clauses.append(clause)
    return clauses, v_count

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

def run_ac3(triplet_data, adj, alive_states):
    # Копируем состояния, чтобы не портить оригинал в рекурсии
    alive = [s.copy() for s in alive_states]
    queue = collections.deque([(i, j) for i in adj for j, _ in adj[i]])
    
    while queue:
        i, j = queue.popleft()
        common = next(c for n, c in adj[i] if n == j)
        
        to_remove = set()
        for idx_i in alive[i]:
            si_map = triplet_data[i][idx_i]
            supported = False
            for idx_j in alive[j]:
                if all(si_map[v] == triplet_data[j][idx_j][v] for v in common):
                    supported = True
                    break
            if not supported:
                to_remove.add(idx_i)
        
        if to_remove:
            alive[i] -= to_remove
            if not alive[i]: return None # Локальный UNSAT
            for k, _ in adj[i]:
                if k != j: queue.append((k, i))
    return alive

def run_bdd_final(triplet_data, adj, result):
    """Финальная проверка остатка через BDD"""
    total_s = sum(len(s) for s in result)
    lbdd = BDD()
    lbdd.configure(reordering=False)
    f_res = lbdd.true
    
    ordered_res = [sorted(list(s)) for s in result]
    v_map = {}
    
    for t_idx, s_list in enumerate(ordered_res):
        if not s_list: continue
        choice = lbdd.false
        v_list = []
        for s_idx in s_list:
            v_name = f"t{t_idx}_s{s_idx}"
            lbdd.declare(v_name)
            v_list.append(lbdd.var(v_name))
            choice |= lbdd.var(v_name)
        f_res &= choice
        v_map[t_idx] = v_list

    for i, neighbors in adj.items():
        for j, common in neighbors:
            if i >= j or i not in v_map or j not in v_map: continue
            for pi, ri in enumerate(ordered_res[i]):
                for pj, rj in enumerate(ordered_res[j]):
                    if any(triplet_data[i][ri][v] != triplet_data[j][rj][v] for v in common):
                        f_res &= (~v_map[i][pi] | ~v_map[j][pj])
                        if f_res == lbdd.false: return False
    return f_res != lbdd.false

def solve_recursive(triplet_data, adj, current_alive, depth=1):
    count = sum(len(s) for s in current_alive)
    
    # 1. Порог для BDD (если состояний мало - добиваем)
    if count < 400:
        return run_bdd_final(triplet_data, adj, current_alive)
    
    # 2. Выбор следующего рычага (самая жирная тройка)
    # Игнорируем тройки, где уже осталось 1 состояние
    candidates = [i for i in range(len(current_alive)) if len(current_alive[i]) > 1]
    if not candidates: 
        return True # Все тройки по 1 состоянию и AC3 прошел -> SAT
    
    target_idx = max(candidates, key=lambda i: len(current_alive[i]))
    
    prefix = "  " * depth
    print(f"{prefix}Уровень {depth}: Тройка №{target_idx} ({len(current_alive[target_idx])} сост.), Всего: {count}")
    
    # Сортируем состояния по "влиятельности" (опционально)
    for s_idx in sorted(list(current_alive[target_idx])):
        next_alive = [s.copy() for s in current_alive]
        next_alive[target_idx] = {s_idx}
        
        # Лавина фильтрации
        filtered = run_ac3(triplet_data, adj, next_alive)
        
        if filtered is not None:
            if solve_recursive(triplet_data, adj, filtered, depth + 1):
                return True
    return False

def main():
    if len(sys.argv) < 2: return
    file_path = sys.argv[1]
    clauses, _ = load_dimacs(file_path)
    triplets = get_triplets(clauses)
    
    print(f"--- Матрёшка-Пробойник: {file_path} ---")
    triplet_data, triplet_vars = [], []
    adj = collections.defaultdict(list)
    
    for t in triplets:
        states, v_list = get_valid_states(t)
        triplet_data.append(states); triplet_vars.append(set(v_list))

    for i, j in combinations(range(len(triplets)), 2):
        common = triplet_vars[i] & triplet_vars[j]
        if common:
            adj[i].append((j, common)); adj[j].append((i, common))

    start_time = time.time()
    base_alive = [set(range(len(td))) for td in triplet_data]
    base_alive = run_ac3(triplet_data, adj, base_alive)
    
    if base_alive is None:
        print("UNSAT на этапе пре-фильтрации!")
    else:
        result = solve_recursive(triplet_data, adj, base_alive)
        print("-" * 30)
        print(f"ИТОГ: {'SAT' if result else 'UNSAT'}")
    
    print(f"Время выполнения: {time.time() - start_time:.2f} сек.")

if __name__ == "__main__":
    main()
