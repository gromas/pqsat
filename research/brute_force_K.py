import os
import sys
import time
from collections import defaultdict

# ============================================================
# Базовые функции
# ============================================================

def parse_dimacs(file_path):
    clauses, num_vars = [], 0
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', '%', '0')):
                continue
            if line.startswith('p cnf'):
                parts = line.split()
                num_vars = int(parts[2])
                continue
            literals = [int(x) for x in line.split() if x != '0']
            if literals:
                clauses.append(literals)
    return clauses, num_vars

def build_p_set_greedy(clauses, num_vars):
    abs_clauses = [[abs(l) for l in c] for c in clauses]
    curr_cl = [list(c) for c in abs_clauses]
    p_set = []
    while curr_cl:
        counts = defaultdict(int)
        for c in curr_cl:
            for v in c:
                counts[v] += 1
        best_v = max(counts, key=counts.get)
        p_set.append(best_v)
        curr_cl = [c for c in curr_cl if best_v not in c]
    return set(p_set)

def classify_clause(c, P, Q):
    if len(c) != 3:
        return 'other'
    p_count = sum(1 for l in c if abs(l) in P)
    if p_count == 3:
        return 'P3'
    elif p_count == 2:
        return 'P2Q1'
    elif p_count == 1:
        return 'P1Q2'
    return 'other'

def greedy_vertex_cover_hypergraph(p3_clauses, p_list):
    p3_copy = [list(set(abs(l) for l in c)) for c in p3_clauses]
    cover = set()
    temp = [list(c) for c in p3_copy]
    while temp:
        counts = defaultdict(int)
        for c in temp:
            for v in c:
                counts[v] += 1
        best_v = max(counts, key=counts.get)
        cover.add(best_v)
        temp = [c for c in temp if best_v not in c]
    return cover

def unit_propagation_full(clauses, assignment):
    """Полный UP с предварительной фиксацией"""
    working = []
    for c in clauses:
        new_c = []
        satisfied = False
        for lit in c:
            var = abs(lit)
            if var in assignment:
                val = assignment[var]
                if (lit > 0 and val) or (lit < 0 and not val):
                    satisfied = True
                    break
            else:
                new_c.append(lit)
        if satisfied:
            continue
        if not new_c:
            return None, None, True
        working.append(new_c)
    
    assign = assignment.copy()
    changed = True
    
    while changed:
        changed = False
        for c in working:
            if len(c) == 1:
                lit = c[0]
                var = abs(lit)
                val = lit > 0
                
                if var in assign:
                    if assign[var] != val:
                        return None, None, True
                    continue
                
                assign[var] = val
                changed = True
                
                new_working = []
                for cl in working:
                    if cl == c:
                        continue
                    new_c = []
                    satisfied = False
                    for l in cl:
                        if abs(l) == var:
                            if (l > 0 and val) or (l < 0 and not val):
                                satisfied = True
                                break
                            continue
                        new_c.append(l)
                    if satisfied:
                        continue
                    if not new_c:
                        return None, None, True
                    new_working.append(new_c)
                working = new_working
                break
    
    return working, assign, False

def build_implication_graph(binary_clauses, assignment):
    """Строит граф импликаций для 2-КНФ части"""
    max_var = 0
    for c in binary_clauses:
        for lit in c:
            max_var = max(max_var, abs(lit))
    
    n = max_var
    adj = [[] for _ in range(2 * n)]
    
    for c in binary_clauses:
        if len(c) == 2:
            a, b = c
            a_node = 2 * (abs(a) - 1) + (0 if a > 0 else 1)
            b_node = 2 * (abs(b) - 1) + (0 if b > 0 else 1)
            adj[a_node ^ 1].append(b_node)
            adj[b_node ^ 1].append(a_node)
        elif len(c) == 1:
            a = c[0]
            a_node = 2 * (abs(a) - 1) + (0 if a > 0 else 1)
            adj[a_node ^ 1].append(a_node)
    
    return adj, n

def find_scc(adj, n):
    """Тарьян для графа импликаций"""
    index = 0
    indices = [-1] * (2 * n)
    lowlink = [0] * (2 * n)
    on_stack = [False] * (2 * n)
    stack = []
    scc_id = [-1] * (2 * n)
    scc_count = 0
    scc_sizes = []
    
    def strongconnect(v):
        nonlocal index, scc_count
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack[v] = True
        
        for w in adj[v]:
            if indices[w] == -1:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack[w]:
                lowlink[v] = min(lowlink[v], indices[w])
        
        if lowlink[v] == indices[v]:
            size = 0
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc_id[w] = scc_count
                size += 1
                if w == v:
                    break
            scc_sizes.append(size)
            scc_count += 1
    
    for v in range(2 * n):
        if indices[v] == -1:
            strongconnect(v)
    
    return scc_sizes, scc_id, scc_count


# ============================================================
# Брутфорс по K
# ============================================================

def brute_force_K(file_path):
    print(f"\n{'='*70}")
    print(f"Брутфорс по K (полный перебор назначений)")
    print(f"Файл: {os.path.basename(file_path)}")
    print('='*70)
    
    clauses, num_vars = parse_dimacs(file_path)
    if not clauses:
        return
    
    # 1. Находим P, Q, P3, K
    P = build_p_set_greedy(clauses, num_vars)
    Q = set(range(1, num_vars + 1)) - P
    p_list = sorted(P)
    
    p3_clauses = [c for c in clauses if classify_clause(c, P, Q) == 'P3']
    if not p3_clauses:
        print("Нет P3 клауз")
        return
    
    K = greedy_vertex_cover_hypergraph(p3_clauses, p_list)
    K_list = sorted(K)
    total = 1 << len(K_list)
    
    print(f"|K| = {len(K)}")
    print(f"Всего назначений: {total:,}")
    print()
    
    # Статистика
    conflict_up = 0
    no_binary = 0
    scc_stats = []
    
    start_time = time.time()
    
    for bits in range(total):
        # Назначение K
        assignment = {}
        for i, var in enumerate(K_list):
            assignment[var] = (bits >> i) & 1
        
        # UP
        remaining, up_assignment, conflict = unit_propagation_full(clauses, assignment)
        if conflict:
            conflict_up += 1
            continue
        
        assignment.update(up_assignment)
        
        # Собираем бинарные клаузы
        binary = []
        for c in remaining:
            if len(c) == 2:
                new_c = []
                satisfied = False
                for lit in c:
                    var = abs(lit)
                    if var in assignment:
                        val = assignment[var]
                        if (lit > 0 and val) or (lit < 0 and not val):
                            satisfied = True
                            break
                    else:
                        new_c.append(lit)
                if satisfied:
                    continue
                if new_c:
                    binary.append(new_c)
        
        if not binary:
            no_binary += 1
            continue
        
        # SCC анализ
        adj, n = build_implication_graph(binary, assignment)
        scc_sizes, scc_id, scc_count = find_scc(adj, n)
        
        # Конфликт в SCC?
        scc_conflict = False
        for i in range(n):
            if scc_id[2 * i] == scc_id[2 * i + 1]:
                scc_conflict = True
                break
        
        non_trivial = sum(1 for s in scc_sizes if s > 1)
        compression = (2 * n) / scc_count if scc_count > 0 else 0
        
        scc_stats.append({
            'bits': bits,
            'scc_count': scc_count,
            'non_trivial': non_trivial,
            'compression': compression,
            'scc_conflict': scc_conflict
        })
        
        # Прогресс
        if bits % max(1, total // 100) == 0:
            pct = bits / total * 100
            elapsed = time.time() - start_time
            eta = (elapsed / max(1, bits)) * (total - bits) if bits > 0 else 0
            print(f"  Прогресс: {bits}/{total} ({pct:.1f}%) | ETA: {eta:.1f}s", end='\r')
    
    elapsed = time.time() - start_time
    
    # Итоговая статистика
    print(f"\n\n{'='*70}")
    print("РЕЗУЛЬТАТЫ")
    print('='*70)
    print(f"Всего назначений: {total:,}")
    print(f"Конфликт после UP: {conflict_up}/{total} ({conflict_up/total*100:.2f}%)")
    print(f"Нет бинарных клауз: {no_binary}/{total} ({no_binary/total*100:.2f}%)")
    
    if scc_stats:
        avg_scc = sum(s['scc_count'] for s in scc_stats) / len(scc_stats)
        avg_non_trivial = sum(s['non_trivial'] for s in scc_stats) / len(scc_stats)
        avg_compression = sum(s['compression'] for s in scc_stats) / len(scc_stats)
        scc_conflicts = sum(1 for s in scc_stats if s['scc_conflict'])
        
        print(f"\nSCC статистика (по {len(scc_stats)} веткам с бинарными клаузами):")
        print(f"  Среднее число SCC: {avg_scc:.1f}")
        print(f"  Среднее число нетривиальных SCC: {avg_non_trivial:.1f}")
        print(f"  Средний коэффициент сжатия: {avg_compression:.2f}")
        print(f"  Конфликт в SCC: {scc_conflicts}/{len(scc_stats)} ({scc_conflicts/len(scc_stats)*100:.1f}%)")
    
    print(f"\nВремя: {elapsed:.2f}s")


def main():
    if len(sys.argv) < 2:
        print("Usage: python brute_force_K.py <file>")
        return
    
    brute_force_K(sys.argv[1])

if __name__ == "__main__":
    main()