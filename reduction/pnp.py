import sys

class PNPSolver:
    def __init__(self, clauses, num_vars):
        self.clauses = [list(set(c)) for c in clauses]  # Убираем дубликаты в дизъюнктах
        self.num_vars = num_vars
        self.multiplexers = {}
        self.is_unsat = False

    def get_cofactors(self, current_clauses, var):
        """Вычисляет кофакторы A (при x=1) и B (при x=0) и остаток R."""
        A, B, R = [], [], []
        
        for clause in current_clauses:
            if var in clause:
                # Если дизъюнкт был (x_i), то после x_i=1 он истинен (исчезает)
                # Но для редукции ABR нам нужны остатки от других литералов в этом дизъюнкте
                remaining = [l for l in clause if l != var]
                if remaining: 
                    A.append(remaining)
                # Если remaining пуст, значит дизъюнкт полностью удовлетворен (x_i = 1)
            elif -var in clause:
                remaining = [l for l in clause if l != -var]
                if not remaining:
                    # Если остался пустой список, значит при x_i=0 дизъюнкт ложен
                    self.is_unsat = True 
                B.append(remaining)
            else:
                R.append(clause)
        return A, B, R

    def solve(self):
        current_clauses = [list(c) for c in self.clauses]
        
        # --- ПРЯМОЙ ХОД ---
        for i in range(1, self.num_vars + 1):
            A, B, R = self.get_cofactors(current_clauses, i)
            self.multiplexers[i] = A
            # Редукция F' = A + B + R (Конъюнкция всех ограничений)
            current_clauses = A + B + R
            
            if [] in current_clauses:
                self.is_unsat = True

        # --- ОБРАТНЫЙ ХОД ---
        assignments = {}
        for i in range(self.num_vars, 0, -1):
            A = self.multiplexers[i]
            
            # Проверяем, удовлетворяет ли кофактор A текущим назначениям
            is_A_satisfied = True
            for clause in A:
                clause_val = False
                for lit in clause:
                    var_idx = abs(lit)
                    if var_idx in assignments:
                        val = assignments[var_idx]
                        if (lit > 0 and val) or (lit < 0 and not val):
                            clause_val = True
                            break
                if not clause_val and any(abs(l) in assignments for l in clause):
                    is_A_satisfied = False
                    break
            
            # Логика: x_i = NOT A
            assignments[i] = not is_A_satisfied

        return assignments

    def verify(self, assignments):
        """Проверяет, сколько дизъюнктов исходной КНФ удовлетворено."""
        satisfied_count = 0
        for clause in self.clauses:
            for lit in clause:
                var = abs(lit)
                val = assignments.get(var, False)
                if (lit > 0 and val) or (lit < 0 and not val):
                    satisfied_count += 1
                    break
        return satisfied_count

def parse_dimacs(filename):
    clauses = []
    num_vars = 0
    with open(filename, 'r') as f:
        for line in f:
            if line.startswith('c') or not line.strip():
                continue
            if line.startswith('p cnf'):
                parts = line.split()
                num_vars = int(parts[2])
                continue
            literals = list(map(int, line.split()))
            if literals and literals[-1] == 0:
                literals.pop()
            if literals:
                clauses.append(literals)
    return clauses, num_vars

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Использование: python pnp.py <file.cnf>")
        sys.exit(1)

    file_path = sys.argv[1]
    clauses, n_vars = parse_dimacs(file_path)
    
    solver = PNPSolver(clauses, n_vars)
    result = solver.solve()
    
    sat_count = solver.verify(result)
    print(f"Файл: {file_path}")
    print(f"Переменных: {n_vars}, Клауз: {len(clauses)}")
    print(f"Статус (внутренний): {'UNSAT' if solver.is_unsat else 'SAT/UNKNOWN'}")
    print(f"Удовлетворено клауз: {sat_count} из {len(clauses)}")
    
    if sat_count == len(clauses):
        print("РЕЗУЛЬТАТ: ГАРАНТИРОВАННЫЙ SAT")
    else:
        print("РЕЗУЛЬТАТ: ЧАСТИЧНОЕ РЕШЕНИЕ (возможен UNSAT или конфликт)")
