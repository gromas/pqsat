import os
import glob
import random
from pathlib import Path

def parse_dimacs_cnf(filepath):
    """
    Парсит DIMACS CNF файл.
    Возвращает: (n, clauses)
    """
    clauses = []
    n = 0
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('%') or line.startswith('0'):
                continue
            if line.startswith('p'):
                parts = line.split()
                if len(parts) >= 3:
                    n = int(parts[2])
                continue
            try:
                nums = list(map(int, line.split()))
            except ValueError:
                continue
            if nums and nums[-1] == 0:
                nums = nums[:-1]
            if nums:
                clauses.append(nums)
    return n, clauses


def load_benchmark_folder(folder_path):
    """
    Загружает все .cnf файлы из папки.
    Возвращает список кортежей (имя_файла, n, clauses)
    """
    benchmarks = []
    cnf_files = glob.glob(os.path.join(folder_path, "*.cnf"))
    
    for cnf_file in cnf_files:
        try:
            n, clauses = parse_dimacs_cnf(cnf_file)
            benchmarks.append((os.path.basename(cnf_file), n, clauses))
        except Exception as e:
            print(f"Ошибка загрузки {cnf_file}: {e}")
    
    return benchmarks


def get_random_benchmark(folder_path):
    """
    Берёт случайный .cnf файл из папки.
    """
    benchmarks = load_benchmark_folder(folder_path)
    if not benchmarks:
        return None
    return random.choice(benchmarks)


def print_benchmark_info(benchmark):
    """
    Красиво выводит информацию о бенчмарке.
    """
    name, n, clauses = benchmark
    print(f"\n{'='*60}")
    print(f"📊 Бенчмарк: {name}")
    print(f"{'='*60}")
    print(f"Переменных: {n}")
    print(f"Дизъюнктов: {len(clauses)}")
    print(f"Плотность: {len(clauses)/n:.2f}")
    
    # Статистика по длинам дизъюнктов
    lengths = [len(c) for c in clauses]
    print(f"\nДлины дизъюнктов:")
    print(f"  min: {min(lengths)}")
    print(f"  max: {max(lengths)}")
    print(f"  среднее: {sum(lengths)/len(lengths):.2f}")
    
    # Первые 5 дизъюнктов для примера
    print(f"\nПервые 5 дизъюнктов:")
    for i, clause in enumerate(clauses[:5]):
        print(f"  {i+1}: {clause}")
    
    return name, n, clauses


# Пример использования
if __name__ == "__main__":
    # Создаём папку для бенчмарков
    bench_dir = "./benchmarks"
    Path(bench_dir).mkdir(exist_ok=True)
    
    # Загружаем уже скачанные
    print(f"\nЗагрузка бенчмарков из {bench_dir}:")
    benchmarks = load_benchmark_folder(bench_dir)
    print(f"Найдено {len(benchmarks)} файлов")
    
    if benchmarks:
        # Показать случайный
        random_bench = random.choice(benchmarks)
        print_benchmark_info(random_bench)
    else:
        print(f"\nПапка {bench_dir} пуста. Поместите туда .cnf файлы.")
        print("\nГде взять бенчмарки:")
        print("1. SATLIB (uf20-91): https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html")
        print("2. SAT Competition Archives: https://satcompetition.github.io/")
        print("3. Zenodo: https://zenodo.org/communities/satcomp/")
