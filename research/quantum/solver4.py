import sys
import time

def parse_cnf(filename):
    clauses, n_vars = [], 0
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'): continue
            if line.startswith('p'):
                parts = line.split()
                n_vars = int(parts[2])
                continue
            if line.startswith(('%', '0')): continue
            c = [int(x) for x in line.split() if x != '0']
            if c: clauses.append(c)
    return clauses, n_vars

def simplify(clauses, lit):
    new_clauses = []
    for c in clauses:
        if lit in c: continue
        new_c = [x for x in c if x != -lit]
        if not new_c: return None # Conflict
        new_clauses.append(new_c)
    return new_clauses

def solve_iterative(clauses, n_vars):
    stack = [(clauses, {})]
    last_phase = {}
    learned_units = set()
    start_t = time.time()

    while stack:
        curr_clauses, assignment = stack.pop()
        
        # 1. Unit Propagation
        changed = True
        while changed:
            changed = False
            # Добавляем выученные ранее юниты
            for unit_lit in learned_units:
                if abs(unit_lit) not in assignment:
                    curr_clauses = simplify(curr_clauses, unit_lit)
                    if curr_clauses is None: break
                    assignment[abs(unit_lit)] = unit_lit
                    changed = True
            
            if curr_clauses is None: break
            
            unit = next((c[0] for c in curr_clauses if len(c) == 1), None)
            if unit:
                assignment[abs(unit)] = unit
                curr_clauses = simplify(curr_clauses, unit)
                if curr_clauses is None: break
                changed = True
        
        if curr_clauses is None: continue # Conflict, пробуем другую ветку
        if not curr_clauses: return assignment # SAT!

        # 2. Выбор детонатора (MOMS)
        weights = {}
        for c in curr_clauses:
            w = 1 / (2**len(c))
            for l in c: weights[l] = weights.get(l, 0) + w
        
        if not weights: continue
        
        best_var = max(weights.keys(), key=lambda l: weights.get(l, 0) + weights.get(-l, 0), default=None)
        if best_var is None: continue
        best_var = abs(best_var)
        
        # Phase Saving
        det = last_phase.get(best_var, best_var if weights.get(best_var, 0) >= weights.get(-best_var, 0) else -best_var)
        
        # 3. Кладём в стек: сначала инверсию, потом прямую фазу
        # (чтобы прямая выскочила первой)
        stack.append((simplify(curr_clauses, -det), {**assignment, best_var: -det}))
        stack.append((simplify(curr_clauses, det), {**assignment, best_var: det}))
        
        # Запоминаем фазу
        last_phase[best_var] = det

    return None

if __name__ == "__main__":
    from datetime import datetime
    print(f"Start time: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}") 
    
    if len(sys.argv) < 2: sys.exit()
    clauses, n_vars = parse_cnf(sys.argv[1])
    print(f"[*] Iterative Collider starting on {n_vars} variables...")
    
    start_time = time.time()
    
    res = solve_iterative(clauses, n_vars)
    
    end_time = time.time()
    
    if res:
        sol = [res.get(i, i) for i in range(1, n_vars + 1)]
        print(f"SAT: {' '.join(map(str, sol))} 0")
    else:
        print("UNSAT")
        
    print(f"\n[!] Time: {end_time - start_time:.4f} seconds")
