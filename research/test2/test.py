import sys
import collections
import numpy as np

def load_cnf(filename):
    clauses = []
    max_var = 0
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', 'p', '%')): 
                if line.startswith('%'): break
                continue
            lits = [int(x) for x in line.split() if int(x) != 0]
            if lits:
                clauses.append(lits)
                max_var = max(max_var, max(abs(l) for l in lits))
    return clauses, max_var

def get_basis_masks(n_basis=6):
    """Создает 64-битные маски для базисных переменных."""
    masks = {}
    for i in range(n_basis):
        v = i + 1
        mask = 0
        for bit in range(64):
            if (bit >> i) & 1:
                mask |= (1 << bit)
        masks[v] = mask
        masks[-v] = ~mask & 0xFFFFFFFFFFFFFFFF
    return masks

def solve_bit_ballet(clauses, n_vars, n_basis=6):
    # 1. Инициализация масок
    # m_true[v] - в каких сценариях v ОБЯЗАН быть True
    m_true = collections.defaultdict(lambda: 0)
    m_false = collections.defaultdict(lambda: 0)
    
    # Базис (первые 6 переменных)
    basis_masks = get_basis_masks(n_basis)
    for v, mask in basis_masks.items():
        if v > 0: m_true[v] = mask
        else: m_false[abs(v)] = mask

    # 2. Распределение клозов
    p1q2 = [] # (p, q1, q2) -> если -p, то (q1 or q2)
    p2q1 = [] # (p1, p2, q) -> если -p1 and -p2, то q=True
    q_pure = [] # (q1, q2)
    
    basis_set = set(range(1, n_basis + 1))
    
    for c in clauses:
        b_lits = [l for l in c if abs(l) in basis_set]
        o_lits = [l for l in c if abs(l) not in basis_set]
        
        if len(b_lits) == 2 and len(o_lits) == 1:
            p2q1.append((b_lits, o_lits[0]))
        elif len(b_lits) == 1 and len(o_lits) == 2:
            p1q2.append((b_lits[0], o_lits))
        elif len(o_lits) == 2 and not b_lits:
            q_pure.append(o_lits)
        elif len(b_lits) == 1 and not o_lits:
            # Юнит в базисе - сразу ограничивает живые сценарии
            pass 

    # 3. Спуск: Заполняем MustBe из P2Q1
    for b_lits, q_lit in p2q1:
        # Условие активации: оба b_lits ложны
        # Т.е. истинны их отрицания
        cond = basis_masks[-b_lits[0]] & basis_masks[-b_lits[1]]
        if q_lit > 0: m_true[abs(q_lit)] |= cond
        else: m_false[abs(q_lit)] |= cond

    # 4. Построение графа импликаций в Q (учитываем P1Q2)
    # adj[откуда] = {куда: маска_сценариев}
    adj = collections.defaultdict(lambda: collections.defaultdict(lambda: 0))
    
    # Статика (чистые 2-КНФ в Q)
    for q1, q2 in q_pure:
        full_mask = 0xFFFFFFFFFFFFFFFF
        adj[-q1][q2] |= full_mask
        adj[-q2][q1] |= full_mask
        
    # Динамика (P1Q2)
    for p_lit, q_lits in p1q2:
        q1, q2 = q_lits
        cond = basis_masks[-p_lit] # Если p ложно
        adj[-q1][q2] |= cond
        adj[-q2][q1] |= cond

    # 5. Битовый Уоршелл (Транзитивное замыкание)
    # Для скорости берем только литералы, участвующие в динамике
    q_nodes = list(adj.keys())
    for k in q_nodes:
        for i in q_nodes:
            if not (adj[i][k]): continue
            for j in q_nodes:
                if adj[k][j]:
                    adj[i][j] |= (adj[i][k] & adj[k][j])

    # 6. Фильтрация "королей"
    valid_scenarios = 0xFFFFFFFFFFFFFFFF
    
    # А) Противоречия из прямых масок (MustTrue & MustFalse)
    for v in range(n_basis + 1, n_vars + 1):
        conflict = m_true[v] & m_false[v]
        valid_scenarios &= ~conflict
        
    # Б) Противоречия из циклов (q -> -q -> q)
    for node in q_nodes:
        # Если в сценарии есть путь q -> -q, то q обязана быть False
        must_be_false_cond = adj[node][-node]
        m_false[abs(node)] |= must_be_false_cond if node > 0 else 0
        m_true[abs(node)] |= must_be_false_cond if node < 0 else 0
        
        # Если есть и q -> -q И -q -> q
        cycle_conflict = adj[node][-node] & adj[-node][node]
        valid_scenarios &= ~cycle_conflict

    return valid_scenarios

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: py test.py <file.cnf>")
        sys.exit(1)
        
    clauses, n_vars = load_cnf(sys.argv[1])
    print(f"--- Bit Ballet Solver ---")
    print(f"Variables: {n_vars}, Clauses: {len(clauses)}")
    
    res_mask = solve_bit_ballet(clauses, n_vars)
    
    count = bin(res_mask).count('1')
    print(f"Valid scenarios for Top-6: {count} / 64")
    
    if res_mask == 0:
        print("RESULT: UNSAT (in current decomposition)")
    else:
        # Ищем первый живой бит
        first_bit = (res_mask & -res_mask).bit_length() - 1
        print(f"RESULT: POTENTIALLY SAT")
        print(f"Example Top-6 Config (bit {first_bit}): ", end="")
        for i in range(6):
            print(f"p{i+1}={(first_bit >> i) & 1}", end=" ")
        print()
