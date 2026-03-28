import os
import sys
import glob
from collections import defaultdict, Counter
from pysat.solvers import Glucose4

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

def classify_clause(c, P):
    if len(c) != 3:
        return False
    return all(abs(l) in P for l in c)

def greedy_vertex_cover(p3_clauses, p_list):
    """Жадное вершинное покрытие для P3"""
    p3_copy = [list(set(abs(l) for l in c)) for c in p3_clauses]
    cover = set()
    temp_clauses = [list(c) for c in p3_copy]
    while temp_clauses:
        counts = defaultdict(int)
        for c in temp_clauses:
            for v in c:
                counts[v] += 1
        best_v = max(counts, key=counts.get)
        cover.add(best_v)
        temp_clauses = [c for c in temp_clauses if best_v not in c]
    return cover

def add_atmost_k(solver, vars_list, k):
    """
    Добавляет ограничение: не более k переменных из vars_list истинны.
    Использует последовательное кодирование (sequential encoding).
    """
    if k >= len(vars_list):
        return
    if k == 0:
        for v in vars_list:
            solver.add_clause([-v])
        return
    
    # Вводим вспомогательные переменные s[i][j]
    # Для простоты используем стандартное кодирование:
    # Для каждой пары переменных добавляем ограничение, что не могут быть обе истинны
    # Это квадратичное кодирование, но для небольших k подойдёт
    from itertools import combinations
    for combo in combinations(vars_list, k+1):
        solver.add_clause([-v for v in combo])

def add_atleast_k(solver, vars_list, k):
    """
    Добавляет ограничение: не менее k переменных из vars_list истинны.
    """
    if k <= 0:
        return
    if k == len(vars_list):
        for v in vars_list:
            solver.add_clause([v])
        return
    
    # Используем стандартное кодирование: хотя бы k из n
    from itertools import combinations
    for combo in combinations(vars_list, len(vars_list) - k + 1):
        solver.add_clause(list(combo))

def find_min_cover_size(P, p3_clauses):
    """
    Находит размер минимального вершинного покрытия P3
    с помощью бинарного поиска и SAT-решателя.
    """
    p_list = sorted(P)
    n = len(p_list)
    
    # Жадное покрытие для верхней границы
    greedy_cover = greedy_vertex_cover(p3_clauses, p_list)
    high = len(greedy_cover)
    print(f"    Жадное покрытие: {high}")
    
    low = 1
    
    def can_cover_with_size(k):
        """Проверяет, существует ли покрытие размера k"""
        solver = Glucose4()
        
        # Ограничение: каждая клауза должна быть покрыта
        for clause in p3_clauses:
            clause_vars = [abs(l) for l in clause]
            solver.add_clause(clause_vars)
        
        # Ограничение: не более k переменных
        add_atmost_k(solver, p_list, k)
        
        result = solver.solve()
        solver.delete()
        return result
    
    # Бинарный поиск
    min_size = high
    while low <= high:
        mid = (low + high) // 2
        if can_cover_with_size(mid):
            min_size = mid
            high = mid - 1
        else:
            low = mid + 1
    
    return min_size

def find_one_min_cover(P, p3_clauses, size):
    """
    Находит одно минимальное покрытие заданного размера.
    """
    p_list = sorted(P)
    solver = Glucose4()
    
    # Каждая клауза должна быть покрыта
    for clause in p3_clauses:
        clause_vars = [abs(l) for l in clause]
        solver.add_clause(clause_vars)
    
    # Ровно size переменных
    add_atmost_k(solver, p_list, size)
    add_atleast_k(solver, p_list, size)
    
    if solver.solve():
        model = solver.get_model()
        cover = sorted([v for v in model if v > 0 and v in P])
        solver.delete()
        return cover
    
    solver.delete()
    return None

def find_all_min_covers(P, p3_clauses, min_size, max_covers=10000):
    """
    Находит все минимальные покрытия заданного размера.
    """
    p_list = sorted(P)
    all_covers = []
    solver = Glucose4()
    
    # Базовые ограничения
    for clause in p3_clauses:
        clause_vars = [abs(l) for l in clause]
        solver.add_clause(clause_vars)
    
    # Ровно min_size переменных
    add_atmost_k(solver, p_list, min_size)
    add_atleast_k(solver, p_list, min_size)
    
    while len(all_covers) < max_covers:
        if not solver.solve():
            break
        
        model = solver.get_model()
        cover = sorted([v for v in model if v > 0 and v in P])
        all_covers.append(cover)
        
        # Запрещаем это конкретное покрытие
        solver.add_clause([-v for v in cover])
    
    return all_covers

def analyze_covers(covers, p_list):
    """
    Анализирует все найденные минимальные покрытия.
    """
    print(f"\n  Анализ {len(covers)} покрытий...")
    
    if not covers:
        print("    Нет покрытий!")
        return None
    
    # Статистика по размерам
    sizes = [len(c) for c in covers]
    print(f"\n  Размер покрытий: {min(sizes)} (все одинаковые)")
    
    # Находим обязательные переменные (входят во все покрытия)
    var_count = Counter()
    for cover in covers:
        for v in cover:
            var_count[v] += 1
    
    mandatory = [v for v in p_list if var_count[v] == len(covers)]
    print(f"\n  Обязательные переменные (входят во все покрытия): {len(mandatory)}")
    if len(mandatory) <= 30:
        print(f"    {mandatory}")
    
    # Находим частоту каждой переменной
    print(f"\n  Частота переменных (в % покрытий):")
    freq = [(v, var_count[v]/len(covers)*100) for v in sorted(p_list)]
    high = [v for v, f in freq if f > 80]
    medium = [v for v, f in freq if 20 <= f <= 80]
    low = [v for v, f in freq if f < 20]
    
    print(f"    Высокая частота (>80%): {len(high)}")
    if len(high) <= 20:
        print(f"      {high}")
    print(f"    Средняя частота (20-80%): {len(medium)}")
    print(f"    Низкая частота (<20%): {len(low)}")
    
    # Показываем несколько примеров покрытий
    print(f"\n  Примеры покрытий (первые 5):")
    for i, cover in enumerate(covers[:5]):
        print(f"    {i+1}: {cover}")
    
    return {
        'count': len(covers),
        'min_size': min(sizes),
        'mandatory': mandatory,
        'mandatory_count': len(mandatory),
    }

def analyze_min_covers(file_path, max_covers=10000):
    """Основная функция"""
    print(f"\n{'='*70}")
    print(f"Анализ минимальных покрытий P3")
    print(f"Файл: {os.path.basename(file_path)}")
    print('='*70)
    
    clauses, num_vars = parse_dimacs(file_path)
    if not clauses:
        return
    
    # Построение P
    P = build_p_set_greedy(clauses, num_vars)
    print(f"\n|P| = {len(P)}")
    
    # Выделяем P3 клаузы
    p3_clauses = [c for c in clauses if classify_clause(c, P)]
    print(f"|P3| = {len(p3_clauses)}")
    
    if not p3_clauses:
        print("Нет P3 клауз")
        return
    
    # Находим размер минимального покрытия
    print(f"\n  Поиск минимального размера покрытия...")
    min_size = find_min_cover_size(P, p3_clauses)
    print(f"    Минимальный размер покрытия: {min_size}")
    
    # Находим все минимальные покрытия
    print(f"\n  Поиск всех минимальных покрытий размера {min_size}...")
    covers = find_all_min_covers(P, p3_clauses, min_size, max_covers)
    print(f"    Найдено {len(covers)} покрытий")
    
    if not covers:
        print("Не найдено покрытий!")
        return
    
    # Анализируем
    p_list = sorted(P)
    stats = analyze_covers(covers, p_list)
    
    # Вывод итогов
    print(f"\n{'='*70}")
    print("ИТОГИ")
    print('='*70)
    print(f"|K_fire| = {min_size} (минимальное вершинное покрытие P3)")
    if stats:
        print(f"Всего минимальных покрытий: {stats['count']}")
        print(f"Обязательных переменных: {stats['mandatory_count']}")
    
    return stats

def main():
    if len(sys.argv) < 2:
        print("Usage: python min_covers.py <file_or_directory> [max_covers]")
        print("  max_covers: максимальное количество покрытий для поиска (default: 10000)")
        return
    
    target = sys.argv[1]
    max_covers = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
    
    if os.path.isdir(target):
        files = glob.glob(os.path.join(target, "*.cnf"))[:5]
        print(f"Найдено {len(files)} файлов, показываем первые 5")
        for f in files:
            analyze_min_covers(f, max_covers)
    else:
        analyze_min_covers(target, max_covers)

if __name__ == "__main__":
    main()
