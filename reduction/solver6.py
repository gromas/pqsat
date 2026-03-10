import sys
import time
import numpy

# Импортируем njit и prange напрямую
from numba import njit, prange

@njit(parallel=True, fastmath=True)
def numba_subsumption(p_arr, n_arr):
    size = len(p_arr)
    # Используем numpy через полное имя внутри njit
    keep = numpy.ones(size, dtype=numpy.uint8)
    combined = p_arr | n_arr
    
    for i in prange(size):
        pi, ni = p_arr[i], n_arr[i]
        ci = combined[i]
        for j in range(i):
            if keep[j] == 0: continue
            cj = combined[j]
            if (cj & ~ci) == 0:
                if (p_arr[j] & pi == p_arr[j]) and (n_arr[j] & ni == n_arr[j]):
                    keep[i] = 0
                    break
    return keep

def compress_bitsets(clauses):
    if not clauses: return []
    # Сортировка по весу (количеству бит)
    unique = sorted(list(set(clauses)), key=lambda x: bin(x[0] | x[1]).count('1'))
    
    p_raw = numpy.array([x[0] for x in unique], dtype=numpy.uint64)
    n_raw = numpy.array([x[1] for x in unique], dtype=numpy.uint64)
    
    mask = numba_subsumption(p_raw, n_raw)
    return [(p_raw[i], n_raw[i]) for i in range(len(mask)) if mask[i]]

def main():
    if len(sys.argv) < 2: return
    
    raw_clauses, n_vars = [], 0
    with open(sys.argv[1], 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', '%', '0')): continue
            if line.startswith('p'):
                parts = line.split()
                # DIMACS: p cnf <vars> <clauses>
                n_vars = int(parts[2])
                continue
            lits = [int(x) for x in line.split() if x != '0']
            if lits:
                p_bits, n_bits = numpy.uint64(0), numpy.uint64(0)
                for l in lits:
                    if l > 0: p_bits |= (numpy.uint64(1) << (l-1))
                    else: n_bits |= (numpy.uint64(1) << (abs(l)-1))
                raw_clauses.append((p_bits, n_bits))

    current_f = compress_bitsets(raw_clauses)
    history = [] 
    remaining_vars = set(range(1, n_vars + 1))
    
    print(f"Анализ {n_vars} переменных (Numba Parallel JIT)...")
    while remaining_vars:
        start_step = time.time()
        
        # Min-Fill эвристика
        best_v, best_score = -1, float('inf')
        for v in remaining_vars:
            bit = numpy.uint64(1) << (v-1)
            c_pos = sum(1 for p, n in current_f if p & bit)
            c_neg = sum(1 for p, n in current_f if n & bit)
            score = c_pos * c_neg
            if score < best_score:
                best_score, best_v = score, v
            if score == 0: break
        
        bit_v = numpy.uint64(1) << (best_v-1)
        pos = [c for c in current_f if c[0] & bit_v]
        neg = [c for c in current_f if c[1] & bit_v]
        rem = [c for c in current_f if not ((c[0] | c[1]) & bit_v)]
        
        history.append((best_v, pos, neg))
        
        res = list(rem)
        for pp, pn in pos:
            rp_p = pp & ~bit_v
            for np, nn in neg:
                rp, rn = rp_p | np, pn | (nn & ~bit_v)
                if not (rp & rn): 
                    res.append((rp, rn))
        
        current_f = compress_bitsets(res)
        remaining_vars.remove(best_v)
        
        if any(p == 0 and n == 0 for p, n in current_f):
            print("UNSAT"); return
            
        print(f"Шаг {len(history)}, дизъюнктов: {len(current_f)}, время: {time.time()-start_step:.4f}s")

    # ОБРАТНЫЙ ХОД (с учетом того, что дизъюнкты с истинными литералами не нужны)
    assign = {}
    print("Восстановление...")
    for v, pos_cls, neg_cls in reversed(history):
        bit_v = numpy.uint64(1) << (v-1)
        can_be_one = True
        
        for p, n in neg_cls:
            satisfied = False
            # Убираем текущую переменную
            m_p, m_n = p, n & ~bit_v
            
            # Проверяем по уже назначенным ("будущим") значениям
            for var_idx, val in assign.items():
                b = numpy.uint64(1) << (var_idx-1)
                if (m_p & b and val) or (m_n & b and not val):
                    satisfied = True
                    break
            
            if not satisfied:
                can_be_one = False
                break
        assign[v] = can_be_one
        
    # Финальный чек
    print ("Проверка решения")
    final_sat = True
    for p, n in raw_clauses:
        clause_sat = False
        for i in range(n_vars):
            b = (1 << i)
            val = assign.get(i+1, False)
            if (p & b and val) or (n & b and not val):
                clause_sat = True; break
        if not clause_sat:
            final_sat = False; break

    print("\nИТОГ:", "SAT" if final_sat else "UNSAT")
    if final_sat:
        print("Набор:", "".join(['1' if assign.get(i, False) else '0' for i in range(1, n_vars+1)]))


if __name__ == "__main__":
    main()
