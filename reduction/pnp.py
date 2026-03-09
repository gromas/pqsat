def solve_pnp_sat(clauses, variables):
    """
    clauses: список множеств (напр. [{"a", "b", "c"}, {"-a", "d"}])
    variables: упорядоченный список переменных ["x1", "x2", ..., "xn"]
    """
    f_history = []  # Храним состояние кофакторов для обратного хода
    current_clauses = [set(c) for c in clauses]

    # ПРЯМОЙ ХОД: Алгебраическая элиминация (Пункт 4)
    for x in variables:
        not_x = "-" + x if not x.startswith("-") else x[1:]
        
        # Разделяем формулу на части A (с x), B (с not_x) и R (остальное)
        A = [c for c in current_clauses if x in c]
        B = [c for c in current_clauses if not_x in c]
        R = [c for c in current_clauses if x not in c and not_x not in c]
        
        # Сохраняем "проекцию" для обратного хода
        # f(x) зависит от того, что осталось в A и R
        f_history.append((x, not_x, list(A), list(R)))
        
        # КОЛЛАПС: F' = (A \ {x}) + (B \ {not_x}) + R
        # Это "бесплатная" редукция без раздувания
        new_A = [c - {x} for c in A]
        new_B = [c - {not_x} for c in B]
        current_clauses = new_A + new_B + R

    # ОБРАТНЫЙ ХОД: Сборка вектора
    values = {}
    # Идем от x_n к x_1
    for x, not_x, A_orig, R_orig in reversed(f_history):
        # Вычисляем f(x) = A * R на уже известных значениях
        # Если хотя бы один клоз в A или R занулился -> бит x = 0
        # Иначе пробуем x = 1 (максимизация)
        
        def check_satisfied(clauses_list, current_values):
            for c in clauses_list:
                # Если в клозе нет ни одного True литерала — он потенциально 0
                resolved = False
                for lit in c:
                    v = lit.strip("-")
                    val = current_values.get(v)
                    if val is not None:
                        is_neg = lit.startswith("-")
                        if (val and not is_neg) or (not val and is_neg):
                            resolved = True; break
                if not resolved and all(l.strip("-") in current_values for l in c):
                    return False # Клоз точно 0
            return True

        # Пробуем положить x = 1
        if check_satisfied(A_orig + R_orig, {**values, x: True}):
            values[x] = True
        else:
            values[x] = False

    # ФИНАЛЬНАЯ ВЕРИФИКАЦИЯ
    is_valid = True
    for c in clauses:
        clause_sat = False
        for lit in c:
            v = lit.strip("-")
            val = values[v]
            if (val and not lit.startswith("-")) or (not val and lit.startswith("-")):
                clause_sat = True; break
        if not clause_sat:
            is_valid = False; break
            
    return values, is_valid

# Пример использования:
# vars = ["a", "b"]
# cls = [{"a", "b"}, {"-a", "b"}]
# result, sat = solve_pnp_sat(cls, vars)
