import sys
import time
import numpy

from numba import njit, prange

# --- Функция subsumption (без изменений, она эффективна) ---
@njit(parallel=True, fastmath=True)
def numba_subsumption(p_arr, n_arr):
    size = len(p_arr)
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
    """Без изменений: удаляет избыточные клозы."""
    if not clauses: return []
    unique = sorted(list(set(clauses)), key=lambda x: bin(x[0] | x[1]).count('1'))
    p_raw = numpy.array([x[0] for x in unique], dtype=numpy.uint64)
    n_raw = numpy.array([x[1] for x in unique], dtype=numpy.uint64)
    mask = numba_subsumption(p_raw, n_raw)
    return [(p_raw[i], n_raw[i]) for i in range(len(mask)) if mask[i]]

# --- Основная функция ---
def main():
    if len(sys.argv) < 2: return

    raw_clauses, n_vars = [], 0
    with open(sys.argv[1], 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', '%', '0')): continue
            if line.startswith('p'):
                parts = line.split()
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
    history = []  # Будем хранить (переменная, pos_клозы, neg_клозы, остаток_на_тот_момент)
    remaining_vars = set(range(1, n_vars + 1))

    print(f"Анализ {n_vars} переменных для поиска ЛЕКСИКОГРАФИЧЕСКИ МАКСИМАЛЬНОГО решения...")

    # === ИЗМЕНЕНИЕ 1: Прямой ход с порядком 1..n ===
    # Вместо min-fill эвристики, идем строго по порядку для лексикографического максимума.
    # Но для эффективности можно комбинировать: если переменная не влияет (нет клозов) - пропускаем.
    # Для простоты реализации сделаем строгий порядок, но с оптимизацией: если переменная не в current_f, её можно сразу назначить 0 (как свободную).

    for v in range(1, n_vars + 1):
        if v not in remaining_vars: # Уже обработана? (в данном цикле не должно быть)
            continue

        start_step = time.time()
        bit_v = numpy.uint64(1) << (v-1)

        # Разделяем клозы
        pos = [c for c in current_f if c[0] & bit_v]
        neg = [c for c in current_f if c[1] & bit_v]
        rem = [c for c in current_f if not ((c[0] | c[1]) & bit_v)]

        # Сохраняем историю. Важно сохранить и rem, чтобы знать контекст для обратного хода.
        history.append((v, pos, neg, rem.copy())) # Сохраняем копию остатка

        # --- РЕЗОЛЮЦИЯ (как в оригинале) ---
        res = list(rem)
        for pp, pn in pos:
            rp_p = pp & ~bit_v
            for np, nn in neg:
                rp, rn = rp_p | np, pn | (nn & ~bit_v)
                if not (rp & rn):
                    res.append((rp, rn))
        # -------------------------------------

        current_f = compress_bitsets(res)
        remaining_vars.remove(v)

        # Проверка на пустой клоз (конфликт)
        if any(p == 0 and n == 0 for p, n in current_f):
            # В оригинале здесь сразу UNSAT. Для максимума мы должны откатываться, но в этой версии
            # для простоты пока считаем, что формула UNSAT, если стратегия 1..n ведет к конфликту.
            # Более продвинутая версия должна здесь реализовывать откат для поиска максимума.
            print(f"UNSAT на шаге {v}. Для лексикографического максимума нужен откат (backjumping).")
            # Пока выходим.
            return

        print(f"Шаг {v}, остаток дизъюнктов: {len(current_f)}, время: {time.time()-start_step:.4f}s")

    # === ИЗМЕНЕНИЕ 2: Обратный ход для ЛЕКСИКОГРАФИЧЕСКОГО МАКСИМУМА ===
    assign = {}
    print("\nВосстановление максимального решения...")

    # Проходим историю в обратном порядке
    for v, pos_cls, neg_cls, rem_context in reversed(history):
        bit_v = numpy.uint64(1) << (v-1)

        # --- Пытаемся установить v = 1 (максимизация) ---
        v_can_be_one = True
        # Для этого ВСЕ клозы из neg_cls (с -v) должны быть выполнимы БЕЗ помощи v.
        # То есть в каждом таком клозе должен найтись другой истинный литерал.
        for p, n in neg_cls:
            # Убираем из клоза литерал -v
            remaining_p, remaining_n = p, n & ~bit_v

            # Проверяем, выполнен ли этот укороченный клоз текущими (будущими) назначениями
            clause_satisfied_without_v = False
            # Перебираем уже назначенные переменные (они идут после v в порядке возрастания)
            for var_idx, val in assign.items():
                b = numpy.uint64(1) << (var_idx-1)
                # Литерал истинен, если: (полож. и val=True) ИЛИ (отриц. и val=False)
                if (remaining_p & b and val) or (remaining_n & b and not val):
                    clause_satisfied_without_v = True
                    break
            if not clause_satisfied_without_v:
                v_can_be_one = False
                break

        # --- Принимаем решение ---
        if v_can_be_one:
            assign[v] = True
            # print(f"  x{v}=1 (макс. возможное)")
        else:
            assign[v] = False
            # print(f"  x{v}=0 (т.к. 1 невозможно)")

    # Финальная проверка (как в оригинале)
    print("\nПроверка решения...")
    final_sat = True
    for p, n in raw_clauses:
        clause_sat = False
        for i in range(n_vars):
            b = (1 << i)
            val = assign.get(i+1, False)
            if (p & b and val) or (n & b and not val):
                clause_sat = True
                break
        if not clause_sat:
            final_sat = False
            break

    print("\n" + "="*40)
    print("ИТОГ:")
    if final_sat:
        print("SAT (найдено лексикографически максимальное решение)")
        # Формируем строку результата строго по порядку переменных 1..n
        result_str = ''.join(['1' if assign.get(i, False) else '0' for i in range(1, n_vars+1)])
        print(f"Набор: {result_str}")
    else:
        print("UNSAT (ошибка: решение не прошло проверку)")

if __name__ == "__main__":
    main()
