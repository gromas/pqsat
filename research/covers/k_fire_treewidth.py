import os
import sys
import glob
import networkx as nx
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

def classify_p3(clauses, P):
    p3 = []
    for c in clauses:
        if len(c) == 3:
            vars_in_c = {abs(l) for l in c}
            if vars_in_c.issubset(P):
                p3.append(c)
    return p3

def build_graph_from_p3(p3_clauses, p_list):
    G = nx.Graph()
    G.add_nodes_from(p_list)
    for clause in p3_clauses:
        vars_in_clause = [abs(l) for l in clause]
        for i in range(len(vars_in_clause)):
            for j in range(i+1, len(vars_in_clause)):
                G.add_edge(vars_in_clause[i], vars_in_clause[j])
    return G

def min_vertex_cover_exact(G):
    """
    Точный алгоритм для вершинного покрытия на маленьких графах.
    Использует бранчинг.
    """
    if not G.edges():
        return []
    
    # Находим ребро
    u, v = list(G.edges())[0]
    
    # Вариант 1: берём u
    G1 = G.copy()
    G1.remove_node(u)
    cover1 = min_vertex_cover_exact(G1)
    cover1.append(u)
    
    # Вариант 2: берём v
    G2 = G.copy()
    G2.remove_node(v)
    cover2 = min_vertex_cover_exact(G2)
    cover2.append(v)
    
    # Выбираем меньшее
    if len(cover1) <= len(cover2):
        return cover1
    else:
        return cover2

def min_vertex_cover_exact_small(G, memo=None):
    """
    Точный алгоритм с мемоизацией.
    """
    if memo is None:
        memo = {}
    
    # Ключ: хеш рёбер
    edges = tuple(sorted(tuple(sorted(e)) for e in G.edges()))
    if edges in memo:
        return memo[edges]
    
    if not edges:
        memo[edges] = []
        return []
    
    # Берём первое ребро
    u, v = edges[0]
    
    # Вариант 1: берём u
    G1 = G.copy()
    G1.remove_node(u)
    cover1 = min_vertex_cover_exact_small(G1, memo).copy()
    cover1.append(u)
    
    # Вариант 2: берём v
    G2 = G.copy()
    G2.remove_node(v)
    cover2 = min_vertex_cover_exact_small(G2, memo).copy()
    cover2.append(v)
    
    if len(cover1) <= len(cover2):
        memo[edges] = cover1
        return cover1
    else:
        memo[edges] = cover2
        return cover2

def estimate_treewidth(G, max_attempts=20):
    """Жадная эвристика для оценки treewidth"""
    import copy
    
    best_width = float('inf')
    for _ in range(max_attempts):
        H = copy.deepcopy(G)
        width = 0
        while H.nodes():
            min_deg = min(dict(H.degree()).values())
            width = max(width, min_deg)
            # Удаляем вершину с минимальной степенью
            candidates = [v for v, d in H.degree() if d == min_deg]
            H.remove_node(candidates[0])
        best_width = min(best_width, width)
    return best_width

def greedy_vertex_cover(p3_clauses, p_list):
    """Жадное вершинное покрытие для P3"""
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

def analyze_via_treewidth(file_path):
    print(f"\n{'='*70}")
    print(f"Анализ K_fire через treewidth и точное вершинное покрытие")
    print(f"Файл: {os.path.basename(file_path)}")
    print('='*70)
    
    clauses, num_vars = parse_dimacs(file_path)
    if not clauses:
        return
    
    P = build_p_set_greedy(clauses, num_vars)
    p_list = sorted(P)
    print(f"\n|P| = {len(P)}")
    
    p3_clauses = classify_p3(clauses, P)
    print(f"|P3| = {len(p3_clauses)}")
    
    if not p3_clauses:
        print("Нет P3 клауз")
        return
    
    G = build_graph_from_p3(p3_clauses, p_list)
    print(f"Граф: {G.number_of_nodes()} вершин, {G.number_of_edges()} рёбер")
    
    tw = estimate_treewidth(G)
    print(f"\nОценка treewidth: {tw}")
    
    # Поиск минимального вершинного покрытия
    print("\nПоиск минимального вершинного покрытия...")
    
    if len(p_list) <= 35:
        cover = min_vertex_cover_exact_small(G)
        print(f"  Точное покрытие: {len(cover)}")
    else:
        print("  Граф слишком большой, используем жадный алгоритм")
        cover = greedy_vertex_cover(p3_clauses, p_list)
        print(f"  Жадное покрытие: {len(cover)}")
    
    greedy_cover = greedy_vertex_cover(p3_clauses, p_list)
    print(f"\nЖадное покрытие для сравнения: {len(greedy_cover)}")
    
    print(f"\n{'='*70}")
    print("ИТОГИ")
    print('='*70)
    print(f"|K_fire| (минимальное вершинное покрытие P3) = {len(cover)}")
    
    return {
        'name': os.path.basename(file_path),
        '|P|': len(P),
        '|P3|': len(p3_clauses),
        'treewidth': tw,
        '|K_fire|': len(cover),
        'greedy_size': len(greedy_cover)
    }

def batch_analyze(directory, limit=5):
    files = glob.glob(os.path.join(directory, "*.cnf"))
    print(f"Найдено {len(files)} файлов")
    
    if limit:
        files = files[:limit]
        print(f"Показываем первые {limit} файлов")
    
    results = []
    for f in files:
        r = analyze_via_treewidth(f)
        if r:
            results.append(r)
    
    if len(results) > 1:
        print(f"\n{'='*70}")
        print("СВОДКА ПО ФАЙЛАМ")
        print('='*70)
        print(f"{'Файл':<25} {'|P|':<6} {'|P3|':<6} {'Treewidth':<10} {'|K_fire|':<10} {'Greedy'}")
        print("-"*70)
        for r in results:
            print(f"{r['name']:<25} {r['|P|']:<6} {r['|P3|']:<6} {r['treewidth']:<10} {r['|K_fire|']:<10} {r['greedy_size']}")

def main():
    if len(sys.argv) < 2:
        print("Usage: python k_fire_treewidth.py <file_or_directory> [limit]")
        return
    
    target = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    
    if os.path.isdir(target):
        batch_analyze(target, limit)
    else:
        analyze_via_treewidth(target)

if __name__ == "__main__":
    main()
