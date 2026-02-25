import sys
import os
import gc
from dd.autoref import BDD
from collections import defaultdict

class MatryoshkaSolver:
    def __init__(self, cnf_path):
        gc.enable()
        self.bdd = BDD()
        self.clauses = self.load_dimacs(cnf_path)
        self.vars = sorted(list(set(abs(l) for c in self.clauses for l in c)))
        # Регистрируем все переменные в BDD
        for v in self.vars:
            self.bdd.declare(f'x{v}')
        
        print(f"📊 Загружено: {len(self.vars)} переменных, {len(self.clauses)} клозов")
        
        # Строим иерархию уровней
        self.levels = self.decompose_levels()
        # Анализ жизненного цикла переменных
        self.last_appearance = self.analyze_liveness()

    def load_dimacs(self, path):
        clauses = []
        with open(path, 'r') as f:
            for line in f:
                if line.startswith(('c', 'p', '%', '0')) or not line.strip(): 
                    continue
                clause = [int(x) for x in line.split() if x != '0']
                if clause:
                    clauses.append(clause)
        return clauses

    def _find_vertex_cover_for_subset(self, var_subset):
        """Жадное вершинное покрытие для подмножества переменных"""
        if len(var_subset) <= 1:
            return [], list(var_subset)
        
        var_set = set(var_subset)
        edges = set()
        for clause in self.clauses:
            vars_in = [abs(lit) for lit in clause if abs(lit) in var_set]
            if len(vars_in) < 2:
                continue
            for i in range(len(vars_in)):
                for j in range(i+1, len(vars_in)):
                    a, b = sorted([vars_in[i], vars_in[j]])
                    edges.add((a, b))
        
        if not edges:
            return [], list(var_subset)
        
        degree = defaultdict(int)
        for a, b in edges:
            degree[a] += 1
            degree[b] += 1
        
        cover = set()
        uncovered = edges.copy()
        while uncovered and degree:
            max_v = max(degree.items(), key=lambda x: x[1])[0]
            cover.add(max_v)
            to_remove = []
            for e in uncovered:
                if max_v in e:
                    to_remove.append(e)
                    a, b = e
                    degree[a] -= 1
                    degree[b] -= 1
                    if degree[a] == 0: del degree[a]
                    if degree[b] == 0: del degree[b]
            for e in to_remove:
                uncovered.remove(e)
        
        P = list(cover)
        Q = [v for v in var_subset if v not in cover]
        return P, Q

    def _get_bridge_clauses(self, P, Q):
        """Возвращает клозы, связывающие P и Q"""
        P_set = set(P)
        Q_set = set(Q)
        bridges = []
        for clause in self.clauses:
            vars_in = set(abs(l) for l in clause)
            if vars_in & P_set and vars_in & Q_set:
                bridges.append(clause)
        return bridges

    def decompose_levels(self):
        """Строит уровни матрешки P0 → P1 → P2 → ..."""
        print("🏗️ Построение матрешки...")
        levels = []
        current_vars = self.vars.copy()
        depth = 0
        
        while current_vars and depth < 10:
            P, Q = self._find_vertex_cover_for_subset(current_vars)
            if not P:
                levels.append({'P': [], 'Q': current_vars, 'bridges': []})
                break
            
            bridges = self._get_bridge_clauses(P, Q)
            levels.append({
                'P': P,
                'Q': Q,
                'bridges': bridges
            })
            
            print(f"  Уровень {depth}: |P|={len(P)}, |Q|={len(Q)}, мостов={len(bridges)}")
            current_vars = P
            depth += 1
        
        return levels

    def analyze_liveness(self):
        """Определяет последний уровень, где переменная еще нужна."""
        last_lvl = {}
        for lvl_idx, level in enumerate(self.levels):
            for v in level['P'] + level['Q']:
                # Чем больше индекс, тем глубже уровень
                if v not in last_lvl or lvl_idx > last_lvl[v]:
                    last_lvl[v] = lvl_idx
        return last_lvl

    def get_horn_dual_split(self, clauses):
        """Разбивает клозы на Horn (pos <= 1) и Dual Horn (neg <= 1)"""
        horn = []
        dual = []
        for c in clauses:
            pos = sum(1 for x in c if x > 0)
            neg = sum(1 for x in c if x < 0)
            if pos <= 1:
                horn.append(c)
            if neg <= 1:
                dual.append(c)
        # Убираем дубликаты (клозы могут попасть в обе категории)
        horn = [list(x) for x in set(tuple(c) for c in horn)]
        dual = [list(x) for x in set(tuple(c) for c in dual)]
        return horn, dual

    def build_block_bdd(self, clauses):
        """Строит BDD для блока клозов."""
        if not clauses:
            return self.bdd.true
        res = self.bdd.true
        for c in clauses:
            clause_bdd = self.bdd.false
            for lit in c:
                var_name = f'x{abs(lit)}'
                node = self.bdd.var(var_name) if lit > 0 else ~self.bdd.var(var_name)
                clause_bdd |= node
            res &= clause_bdd
        return res

    def solve(self):
        current_bdd = self.bdd.true
        
        # Идем снизу вверх (от самого глубокого уровня к 0)
        for i in reversed(range(len(self.levels))):
            level = self.levels[i]
            P = level['P']
            Q = level['Q']
            bridges = level['bridges']
            
            print(f"\n🚀 Уровень {i}: |P|={len(P)}, |Q|={len(Q)}, мостов={len(bridges)}")
            print(f"   P: {P[:5]}... (первые 5)")
            print(f"   Q: {Q[:5]}...")
            
            # 1. ГОРИЗОНТАЛЬНЫЙ СПЛИТ мостов
            horn_c, dual_c = self.get_horn_dual_split(bridges)
            print(f"   ├─ Horn: {len(horn_c)}, Dual: {len(dual_c)}")
            
            # Обучаем два независимых "полушария"
            if horn_c:
                bdd_horn = self.build_block_bdd(horn_c)
                current_bdd &= bdd_horn
            if dual_c:
                bdd_dual = self.build_block_bdd(dual_c)
                current_bdd &= bdd_dual
            
            # 2. ЭЛИМИНАЦИЯ Q (Независимое множество)
            if Q:
                print(f"   ├─ Элиминация Q: {len(Q)} переменных")
                q_vars = [f'x{q}' for q in Q]
                current_bdd = self.bdd.exist(q_vars, current_bdd)
            
            # 3. LIVENESS: Элиминация мертвых P
            # Переменная мертва, если её последний уровень меньше текущего
            dead_p = [v for v in P if self.last_appearance.get(v, -1) < i]
            if dead_p:
                print(f"   ├─ Очистка мертвых P: {len(dead_p)} шт.")
                dead_vars = [f'x{v}' for v in dead_p]
                current_bdd = self.bdd.exist(dead_vars, current_bdd)
            
            # 4. Мусоросборник и реордер
            self.bdd.collect_garbage()
            if i % 2 == 0:
                self.bdd.configure(reordering=True)
            
            size = len(self.bdd)
            print(f"   └─ BDD: {size:,} узлов")
            
            if current_bdd == self.bdd.false:
                print("   ❌ UNSAT DETECTED!")
                return "UNSAT"
        
        # Финальная проверка
        if current_bdd == self.bdd.false:
            return "UNSAT"
        if current_bdd == self.bdd.true:
            return "SAT"
        
        # Пробуем найти модель
        try:
            next(self.bdd.pick_iter(current_bdd))
            return "SAT"
        except StopIteration:
            return "UNSAT"

# Запуск
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: py matryoshka_v2.py <file.cnf>")
        sys.exit(1)
    
    solver = MatryoshkaSolver(sys.argv[1])
    result = solver.solve()
    print(f"\n{'='*60}")
    print(f"🎯 РЕЗУЛЬТАТ: {result}")
