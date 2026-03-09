import sys
import time

def parse_dimacs(filename):
    """Парсер DIMACS CNF файлов"""
    clauses = []
    variables = set()
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('p'):
                continue
            # Читаем литералы до нуля
            lits = [int(x) for x in line.split()[:-1]]
            clauses.append(set(lits))
            for l in lits:
                variables.add(abs(l))
    return clauses, sorted(list(variables))
    
def solve_pnp_sat_strict(clauses, var_list):
    f_history = []
    current_clauses = [set(c) for c in clauses]

    # --- ПРЯМОЙ ХОД: F' = A * R (Коллапс по п. 4) ---
    for x in var_list:
        not_x = -x
        
        # A: клозы с x, B: клозы с -x, R: остальные
        A = [c for c in current_clauses if x in c]
        B = [c for c in current_clauses if not_x in c]
        R = [c for c in current_clauses if x not in c and not_x not in c]
        
        # Функция саморедукции f(x) = A v B
        # Сохраняем и A, и B для обратного хода (как части одной функции)
        A_stripped = [c - {x} for c in A]
        B_stripped = [c - {not_x} for c in B]
        f_history.append((x, A_stripped, B_stripped))
        
        # РЕДУКЦИЯ: B полностью элиминируется. Остается только A и R.
        # Это предотвращает рост формулы.
        current_clauses = A_stripped + R

    # --- ОБРАТНЫЙ ХОД: x_i = f(x_{i+1}...x_n) = (A v B) ---
    values = {}
    for x, A_s, B_s in reversed(f_history):
        # Проверяем f(x) = (A v B) на уже известных переменных справа
        # Если хотя бы один клоз в A И хотя бы один в B "упали" в 0, 
        # значит f(x) = 0. Иначе x = 1 (максимизация).
        
        def is_part_satisfied(part):
            for clause in part:
                if not clause: return False # Пустой клоз — это 0
                sat = False
                for lit in clause:
                    v_id = abs(lit)
                    if v_id in values:
                        val = values[v_id]
                        if (lit > 0 and val) or (lit < 0 and not val):
                            sat = True; break
                # Если клоз полностью определен и в нем нет True — он 0
                if not sat and all(abs(l) in values for l in clause):
                    return False
            return True

        # f(x) = A v B. Если оба кофактора противоречивы — x = 0.
        if is_part_satisfied(A_s) or is_part_satisfied(B_s):
            values[x] = True
        else:
            values[x] = False

    return values

def solve_pnp_sat(clauses, var_list):
    """
    Реализация алгоритма PNP (п. 4):
    Прямой ход: элиминация переменных (удаление литералов).
    Обратный ход: вычисление через кофактор A.
    """
    f_history = []
    current_clauses = [set(c) for c in clauses]

    # --- ПРЯМОЙ ХОД (Синтез функций) ---
    for x in var_list:
        not_x = -x
        
        # A: клозы с x, B: клозы с -x, R: остальные
        A = [c for c in current_clauses if x in c]
        B = [c for c in current_clauses if not_x in c]
        R = [c for c in current_clauses if x not in c and not_x not in c]
        
        # Сохраняем кофактор A для обратного хода
        # Важно: сохраняем A БЕЗ самого x, так как мы проверяем остаток клоза
        f_history.append((x, [c - {x} for c in A]))
        
        # КОЛЛАПС (п. 4): F' = (A \ {x}) + (B \ {-x}) + R
        # Сложность формулы (кол-во литералов) только уменьшается
        new_A = [c - {x} for c in A]
        new_B = [c - {not_x} for c in B]
        current_clauses = new_A + new_B + R

    # --- ОБРАТНЫЙ ХОД (Вычисление вектора) ---
    values = {} # {var_id: True/False}
    
    for x, A_stripped in reversed(f_history):
        # x_i = 1, если f(x_i) = 1.
        # f(x_i) — это значение кофактора A на уже известных x_{i+1}...x_n
        
        is_f_true = True
        for clause in A_stripped:
            # Если в клозе уже есть хотя бы один True литерал — клоз удовлетворен.
            # Если в клозе все определенные литералы False — клоз 0.
            clause_satisfied = False
            for lit in clause:
                v_id = abs(lit)
                if v_id in values:
                    val = values[v_id]
                    # Литерал истинен, если (положительный и True) или (отрицательный и False)
                    if (lit > 0 and val) or (lit < 0 and not val):
                        clause_satisfied = True
                        break
            
            # Если хоть один клоз в кофакторе точно "упал" в 0, f(x_i) становится 0
            # (Здесь мы считаем, что неопределенные переменные — это потенциальные 1)
            if not clause_satisfied and all(abs(l) in values for l in clause):
                is_f_true = False
                break
        
        # Присваиваем значение x_i
        values[x] = is_f_true

    return values

def verify(clauses, values):
    """Финальная проверка решения"""
    for c in clauses:
        satisfied = False
        for lit in c:
            v_id = abs(lit)
            val = values.get(v_id)
            if (lit > 0 and val) or (lit < 0 and not val):
                satisfied = True
                break
        if not satisfied:
            return False
    return True

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python pnp_solver.py <file.cnf>")
        sys.exit(1)

    file_path = sys.argv[1]
    clauses, var_list = parse_dimacs(file_path)
    
    print(f"--- Запуск PNP SAT Solver ---")
    print(f"Файл: {file_path}")
    print(f"Переменных: {len(var_list)}, Клозов: {len(clauses)}")
    
    start_time = time.time()
    solution = solve_pnp_sat(clauses, var_list)
    end_time = time.time()
    
    is_sat = verify(clauses, solution)
    
    print(f"\nРезультат: {'SAT' if is_sat else 'UNSAT (или решение не найдено)'}")
    print(f"Время вычисления: {end_time - start_time:.4f} сек.")
    
    if is_sat:
        # Вывод первых 10 значений для примера
        sample = {k: solution[k] for k in list(solution)[:10]}
        print(f"Пример вектора: {sample}...")
