import os
import sys
import glob
import random
from collections import defaultdict

def parse_dimacs(file_path):
    clauses, num_vars = [], 0
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
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
    except Exception as e:
        print(f"Error parsing {file_path}: {e}")
        return [], 0
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
        if not counts:
            break
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
    else:
        return 'other'

def greedy_vertex_cover_hypergraph(p3_clauses, p_list):
    """Жадное вершинное покрытие для гиперграфа P3"""
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
    """Полный unit propagation"""
    working = [list(c) for c in clauses]
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
                
                # Обновляем клаузы
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

def compute_priority_list(file_path, num_trials=100):
    """
    Вычисляет топ-20 переменных по комбинированному Score.
    Возвращает список приоритетных переменных.
    """
    print(f"\n{'='*70}")
    print(f"Вычисление Score-листа для {os.path.basename(file_path)}")
    print('='*70)
    
    clauses, num_vars = parse_dimacs(file_path)
    if not clauses:
        return []
    
    # Построение P
    P = build_p_set_greedy(clauses, num_vars)
    Q = set(range(1, num_vars + 1)) - P
    p_list = sorted(P)
    
    print(f"|P| = {len(P)}, |Q| = {len(Q)}")
    
    # Выделяем P3 клаузы
    p3_clauses = [c for c in clauses if classify_clause(c, P, Q) == 'P3']
    print(f"|P3| = {len(p3_clauses)}")
    
    if not p3_clauses:
        print("Нет P3 клауз")
        return []
    
    # K_fire = вершинное покрытие P3
    K_fire = greedy_vertex_cover_hypergraph(p3_clauses, p_list)
    print(f"|K_fire| = {len(K_fire)}")
    
    # Строим граф P3 для центральности
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from(p_list)
    for clause in p3_clauses:
        vars_in_clause = [abs(l) for l in clause]
        for i in range(len(vars_in_clause)):
            for j in range(i+1, len(vars_in_clause)):
                G.add_edge(vars_in_clause[i], vars_in_clause[j])
    
    centrality = nx.degree_centrality(G)
    
    # Считаем плотность ограничений
    total_clauses = len(clauses)
    clause_count = defaultdict(int)
    for c in clauses:
        for lit in c:
            clause_count[abs(lit)] += 1
    density = {v: clause_count.get(v, 0) / total_clauses for v in K_fire}
    
    # Считаем вхождение в P2Q1 и P1Q2 (вес мостов)
    p2q1_count = defaultdict(int)
    p1q2_count = defaultdict(int)
    for c in clauses:
        ctype = classify_clause(c, P, Q)
        for lit in c:
            var = abs(lit)
            if ctype == 'P2Q1':
                p2q1_count[var] += 1
            elif ctype == 'P1Q2':
                p1q2_count[var] += 1
    
    # Комбинированный Score
    scores = {}
    for v in K_fire:
        score = centrality.get(v, 0) + density.get(v, 0)
        # Бонус за мосты
        score += 0.5 * (p2q1_count.get(v, 0) / max(p2q1_count.values() or [1]))
        score += 0.3 * (p1q2_count.get(v, 0) / max(p1q2_count.values() or [1]))
        scores[v] = score
    
    # Сортируем
    sorted_vars = sorted(K_fire, key=lambda x: scores[x], reverse=True)
    
    print(f"\nТоп-20 Score-листа:")
    print(f"{'#':<4} {'Var':<6} {'Centrality':<12} {'Density':<10} {'P2Q1':<8} {'P1Q2':<8} {'Score':<8}")
    print("-"*70)
    for i, v in enumerate(sorted_vars[:20]):
        print(f"{i+1:<4} x{v:<5} {centrality.get(v, 0):<12.4f} {density.get(v, 0):<10.4f} {p2q1_count.get(v, 0):<8} {p1q2_count.get(v, 0):<8} {scores[v]:<8.4f}")
    
    return sorted_vars, K_fire, P, Q, p3_clauses

def measure_propagation_rate(file_path, priority_vars, num_trials=100):
    """
    Замеряет, сколько переменных фиксирует UP после фиксации топ-k переменных.
    """
    clauses, num_vars = parse_dimacs(file_path)
    
    print(f"\n{'='*70}")
    print(f"Propagation Rate для {os.path.basename(file_path)}")
    print('='*70)
    print(f"Топ-5 переменных: {priority_vars[:5]}")
    
    total_ternary = len([c for c in clauses if len(c) == 3])
    
    for k in [1, 2, 3, 4, 5]:
        fixed_set = priority_vars[:k]
        propagation_counts = []
        ternary_remaining = []
        
        for _ in range(num_trials):
            assignment = {v: random.choice([True, False]) for v in fixed_set}
            
            # Запускаем UP
            new_clauses, new_assignment, conflict = unit_propagation_full(clauses, assignment)
            
            if conflict:
                propagation_counts.append(0)
                ternary_remaining.append(total_ternary)
            else:
                propagation_counts.append(len(new_assignment) - len(fixed_set))
                # Считаем оставшиеся тернарные клаузы
                ternary = 0
                for c in new_clauses:
                    if len(c) == 3:
                        ternary += 1
                ternary_remaining.append(ternary)
        
        avg_prop = sum(propagation_counts) / len(propagation_counts)
        avg_ternary = sum(ternary_remaining) / len(ternary_remaining)
        print(f"\n  Фиксация {k} переменных:")
        print(f"    UP фиксирует ещё {avg_prop:.1f} переменных (всего {k + avg_prop:.0f})")
        print(f"    Осталось тернарных клауз: {avg_ternary:.0f} из {total_ternary} ({avg_ternary/total_ternary*100:.1f}%)")
        
        if avg_prop > 15:
            print(f"    ✅ ЛАВИНА! Одна переменная фиксирует {avg_prop/k:.1f} других")
        elif avg_prop > 5:
            print(f"    ⚡ Хорошее распространение")
        else:
            print(f"    ⚠️ Слабое распространение")

def batch_analyze(directory, limit=5, num_trials=50):
    """Анализ всех файлов в директории"""
    files = glob.glob(os.path.join(directory, "*.cnf"))
    print(f"Найдено {len(files)} файлов")
    
    if limit:
        files = files[:limit]
        print(f"Показываем первые {limit} файлов")
    
    for f in files:
        priority, K_fire, P, Q, p3 = compute_priority_list(f)
        if priority:
            measure_propagation_rate(f, priority, num_trials)

def main():
    if len(sys.argv) < 2:
        print("Usage: python propagation_rate.py <file_or_directory> [limit] [trials]")
        return
    
    target = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 50
    
    if os.path.isdir(target):
        batch_analyze(target, limit, trials)
    else:
        priority, _, _, _, _ = compute_priority_list(target)
        if priority:
            measure_propagation_rate(target, priority, trials)

if __name__ == "__main__":
    main()
