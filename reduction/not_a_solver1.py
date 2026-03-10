import sys
import time

def parse_dimacs(filename):
    """Парсер DIMACS CNF файлов"""
    clauses = []
    variables = set()
    try:
        with open(filename, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('c') or line.startswith('p'):
                    continue
                lits = [int(x) for x in line.split()[:-1]]
                if lits:
                    clauses.append(set(lits))
                    for l in lits:
                        variables.add(abs(l))
        return clauses, sorted(list(variables))
    except Exception as e:
        print(f"Ошибка при чтении файла: {e}")
        sys.exit(1)

def solve_pnp_sat_vc(clauses, var_list):
    """
    Реализация PNP через логику Вершинного Покрытия:
    Прямой ход: F' = B * R (выбрасываем положительный кофактор A)
    Обратный ход: x_i = 1, если в кофакторе A остались незакрытые дыры (все 0)
    """
    f_history = []
    # Работаем со списком множеств для скорости
    current_clauses = [set(c) for c in clauses]

    # --- ПРЯМОЙ ХОД (Синтез "карты покрытия") ---
    for x in var_list:
        not_x = -x
        
        # A: клозы, где x положительный (x v C)
        # B: клозы, где x отрицательный (-x v C)
        # R: клозы без x
        A = [c for c in current_clauses if x in c]
        B = [c for c in current_clauses if not_x in c]
        R = [c for c in current_clauses if x not in c and not_x not in c]
        
        # Сохраняем "остатки" кофактора A (без самой x)
        # Именно они должны быть "покрыты" будущими переменными
        A_stripped = [c - {x} for c in A]
        f_history.append((x, A_stripped))
        
        # ЭЛИМИНАЦИЯ (Твой коллапс): 
        # Положительные клозы (A) уходят в функцию саморедукции.
        # В основном потоке остаются только B (уже без -x) и R.
        B_stripped = [c - {not_x} for c in B]
        current_clauses = B_stripped + R

    # --- ОБРАТНЫЙ ХОД (Заполнение дыр) ---
    values = {} # {var_id: True/False}
    
    for x, A_stripped in reversed(f_history):
        # Логика: x = 1 только если кофактор A не покрыт переменными справа.
        # То есть, если в A есть хотя бы один клоз, где ВСЕ литералы уже 0.
        
        must_be_one = False
        for clause in A_stripped:
            if not clause: # Если клоз был (x) и стал пустым — это дыра!
                must_be_one = True
                break
            
            # Проверяем, "жив" ли клоз за счет переменных x_{i+1}...x_n
            is_already_covered = False
            for lit in clause:
                v_id = abs(lit)
                if v_id in values:
                    val = values[v_id]
                    # Литерал истинен (покрыт)
                    if (lit > 0 and val) or (lit < 0 and not val):
                        is_already_covered = True
                        break
            
            # Если клоз полностью определен и в нем нет ни одной 1 — это дыра
            if not is_already_covered and all(abs(l) in values for l in clause):
                must_be_one = True
                break
        
        # Если нашли дыру — берем x в покрытие
        values[x] = must_be_one

    return values

def verify(clauses, values):
    """Финальная проверка решения"""
    for c in clauses:
        satisfied = False
        for lit in c:
            v_id = abs(lit)
            val = values.get(v_id, False)
            if (lit > 0 and val) or (lit < 0 and not val):
                satisfied = True
                break
        if not satisfied:
            return False
    return True

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Использование: python pnp_solver.py <file.cnf>")
        sys.exit(1)

    file_path = sys.argv[1]
    clauses, var_list = parse_dimacs(file_path)
    
    print(f"--- PNP SAT Solver (Vertex Cover Logic) ---")
    print(f"Файл: {file_path}")
    print(f"Переменных: {len(var_list)}, Клозов: {len(clauses)}")
    
    start_time = time.perf_counter()
    solution = solve_pnp_sat_vc(clauses, var_list)
    end_time = time.perf_counter()
    
    is_sat = verify(clauses, solution)
    
    print(f"\nСтатус: {'[ OK ] SAT' if is_sat else '[ !! ] UNSAT/FAIL'}")
    print(f"Время: {end_time - start_time:.6f} сек.")
    
    if is_sat:
        # Выведем первые 5 переменных
        print("Пример решения:", {k: solution[k] for k in var_list[:5]})
