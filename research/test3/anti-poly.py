import os
import sys
import glob
import time
from collections import defaultdict

def parse_dimacs(file_path):
    clauses, num_vars = [], 0
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', '%', '0')): continue
            if line.startswith('p cnf'):
                parts = line.split()
                num_vars = int(parts[2])
                continue
            parts = [int(x) for x in line.split() if x != '0']
            if parts: clauses.append(parts)
    return clauses, num_vars

class AntiZhigalkinAnalyser:
    def __init__(self, clauses, num_vars):
        self.clauses = clauses
        self.num_vars = num_vars

    def analyze_algebra(self):
        # 1. Поиск бинарного скелета (2-КНФ составляющие)
        # В твоем представлении !a + !a*b + !a*!b*c = 0
        # Любое слагаемое вида !a*b — это потенциальная бинарная связь
        binary_pairs = set()
        for c in self.clauses:
            if len(c) >= 2:
                # Берем первые две переменные в порядке клоза
                u, v = abs(c[0]), abs(c[1])
                binary_pairs.add(tuple(sorted((u, v))))

        # 2. XOR-сумма (Линейные мономы)
        # Считаем, сколько раз каждая переменная была бы "ведущей" (!a)
        # Если переменная стоит первой в нечетном количестве клозов, она - линейный моном
        lead_counts = defaultdict(int)
        for c in self.clauses:
            if c: lead_counts[abs(c[0])] += 1
        
        linear_monoms = [v for v, count in lead_counts.items() if count % 2 != 0]

        # 3. Оценка "Ядра" (те, кто не попал в линейную часть и не зажат в 2-КНФ)
        vars_in_2sat = set()
        for u, v in binary_pairs:
            vars_in_2sat.add(u)
            vars_in_2sat.add(v)
            
        algebraic_core = set(range(1, self.num_vars + 1)) - set(linear_monoms)
        
        return {
            "Total_Vars": self.num_vars,
            "Linear_Monoms": len(linear_monoms),
            "Binary_Links": len(binary_pairs),
            "Vars_in_2SAT": len(vars_in_2sat),
            "Core_Size": len(algebraic_core)
        }

def process_folder(folder_path):
    files = glob.glob(os.path.join(folder_path, "*.cnf"))
    if not files:
        print(f"Файлы не найдены в {folder_path}")
        return

    print(f"{'File':<20} | {'V':<4} | {'Lin':<4} | {'2-SAT':<5} | {'Core':<4} | {'Ratio'}")
    print("-" * 60)

    for f in sorted(files):
        clauses, num_vars = parse_dimacs(f)
        analyser = AntiZhigalkinAnalyser(clauses, num_vars)
        res = analyser.analyze_algebra()
        
        ratio = round(res['Core_Size'] / res['Total_Vars'], 2)
        name = os.path.basename(f)[:20]
        
        print(f"{name:<20} | {res['Total_Vars']:<4} | {res['Linear_Monoms']:<4} | {res['Vars_in_2SAT']:<5} | {res['Core_Size']:<4} | {ratio}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Использование: python script.py <путь_к_папке_cnf>")
    else:
        path = sys.argv[1].replace('"', '')
        process_folder(path)
