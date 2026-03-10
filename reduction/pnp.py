import sys

class PNPSolver:
    def __init__(self, clauses, num_vars):
        self.clauses = [list(set(c)) for c in clauses]
        self.num_vars = num_vars
        self.storage = {} # Здесь храним A и B для каждой переменной
        self.is_unsat = False

    def get_cofactors(self, current_clauses, var):
        A, B, R = [], [], []
        for clause in current_clauses:
            if var in clause:
                rem = [l for l in clause if l != var]
                if rem: A.append(rem)
            elif -var in clause:
                rem = [l for l in clause if l != -var]
                if not rem: self.is_unsat = True
                B.append(rem)
            else:
                R.append(clause)
        return A, B, R

    def check_function(self, func_clauses, assignments):
        """Проверяет, истинна ли конъюнкция клауз (ABR) на текущем наборе."""
        if not func_clauses: return True
        for clause in func_clauses:
            clause_sat = False
            for lit in clause:
                v = abs(lit)
                if v in assignments:
                    val = assignments[v]
                    if (lit > 0 and val) or (lit < 0 and not val):
                        clause_sat = True
                        break
                else:
                    # Если переменной еще нет в assignments, считаем, что 
                    # она еще не определена. Для проверки ABR это риск.
                    pass 
            if not clause_sat: return False
        return True

    def solve(self):
        current_clauses = [list(c) for c in self.clauses]
        
        # --- ПРЯМОЙ ХОД: Нижний край (BR) ---
        for i in range(1, self.num_vars + 1):
            A, B, R = self.get_cofactors(current_clauses, i)
            # Сохраняем кофакторы для вычисления f(x) = ABR на обратном ходу
            self.storage[i] = {'A': A, 'B': B}
            
            # Редукция до BR (уходим в нижний край)
            current_clauses = B + R
            if [] in current_clauses: self.is_unsat = True

        # --- ОБРАТНЫЙ ХОД: Проверка гипотезы x = ¬A ---
        assignments = {}
        for i in range(self.num_vars, 0, -1):
            A = self.storage[i]['A']
            B = self.storage[i]['B']
            
            # 1. Вычисляем значение A на текущих assignments
            is_A_true = self.check_function(A, assignments)
            
            # 2. Наше исходное предположение: x = ¬A
            hypothesis_x = not is_A_true
            
            # 3. Проверяем f(x) = ABR. 
            # Поскольку R уже "впитано" в предыдущие шаги, проверяем совместимость A и B
            # подставив наше гипотетическое x.
            # Если x=1, должна быть истинна A. Если x=0, должна быть истинна B.
            current_check_val = is_A_true if hypothesis_x else self.check_function(B, assignments)
            
            if current_check_val:
                # Предположение верно
                assignments[i] = hypothesis_x
            else:
                # Переворот предположения: x = A
                assignments[i] = not hypothesis_x

        return assignments

    def verify(self, assignments):
        satisfied = 0
        for c in self.clauses:
            if any((l > 0 and assignments.get(abs(l))) or (l < 0 and not assignments.get(abs(l))) for l in c):
                satisfied += 1
        return satisfied

def parse_dimacs(filename):
    clauses, n_vars = [], 0
    with open(filename, 'r') as f:
        for line in f:
            if line.startswith('c') or not line.strip(): continue
            if line.startswith('p cnf'):
                n_vars = int(line.split()[2])
                continue
            lits = list(map(int, line.split()))
            if lits and lits[-1] == 0: lits.pop()
            if lits: clauses.append(lits)
    return clauses, n_vars

if __name__ == "__main__":
    if len(sys.argv) < 2: sys.exit(1)
    cls, n = parse_dimacs(sys.argv[1])
    solver = PNPSolver(cls, n)
    res = solver.solve()
    count = solver.verify(res)
    print(f"Загружено: {n} переменных, {len(cls)} клауз")
    print(f"Удовлетворено: {count} / {len(cls)}")
    print("РЕЗУЛЬТАТ:", "SAT" if count == len(cls) else "UNSAT/PARTIAL")
