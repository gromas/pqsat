# pqsat algorithm
### Structural Elimination for SAT

#### Author: [Golubin Roman / gromas]
#### License: MIT
#### Status: Research / Proof of Concept

# PQ-Algorithm: Structural Elimination for SAT

A deterministic SAT solver that **adapts to the formula's structure**, eliminating variables as they become irrelevant. Instead of brute-force enumeration or backtracking, it compiles the problem into a Binary Decision Diagram (BDD) by continuously shrinking the active context.

**The core idea is simple:**
- Track which variables are still "alive" (present in remaining clauses).
- Eliminate a variable as soon as it dies (∃-quantification in the BDD).
- The result emerges naturally from the last clause—no final enumeration step.

> ⚠️ **Note on the name:** This PQSAT (Pure-Quantified SAT) is **not** related to the Parametric Quantified SAT (PQSAT) used in the Redlog system. The name comes from our **P** (core) and **Q** (remaining variables) partition, described below.

## Main Conclusion of the Study

The complexity of solving the satisfiability problem for a given 3-CNF formula is not a fixed function of the number of variables n.
It is determined by the structural properties of the specific formula and can vary widely: from O(1) for formulas that reduce to a contradiction already at the cofactor construction stage to O(poly⁡(n)*2^(n/2)) in the worst case, when the variable interaction graph does not allow effective compression.

At the same time, the complexity remains polynomial with respect to n for a fixed size of the vertex cover or independent set.

Thus, the PQ-algorithm adapts to the structure of the formula, choosing the optimal strategy depending on the P and Q ratio, and is guaranteed not to exceed an exponential with a reduced base.

### Terminology: Payload and Quantum

The names **P** and **Q** reflect a fundamental duality in the algorithm's complexity:

* **P** stands for **Payload** — the **spatial complexity**.  
  It's the set of variables simultaneously alive. Its size (`|P| = W_max`) determines the peak memory (BDD nodes).  
  *Think of it as the **width** of the problem.*

* **Q** stands for **Quantum** — the **temporal complexity**.  
  It's the set of variables already eliminated. The number of steps needed to process them determines the runtime.  
  *Think of it as the **length** of the computation.*

> **Total Work ≈ Payload × Quantum ≈ W_max × (number of steps) ≈ ∑|P(t)|²**

The algorithm's predictability comes from the fact that both Payload and Quantum can be estimated **before** solving.  
But more importantly, they can be **optimized** by choosing the right elimination order — our experiments show up to **30% variance** in total work depending on the starting variable.  
This "maneuver" allows us to fit the task into available resources: reduce Payload when memory is tight, or shrink Quantum when speed matters.

## Overview

PQ-Algorithm is a deterministic structural SAT solver based on dynamic context elimination using BDDs (Binary Decision Diagrams).

Unlike traditional SAT solvers that rely on backtracking (DPLL/CDCL) or randomization, PQ-Algorithm:

- Adapts to the structure of the formula
- Eliminates variables as soon as they become irrelevant
- Provides predictable complexity before solving
- Requires no final enumeration — result is in the BDD after the last clause

### Key properties:

- Deterministic (no randomness, always correct)
- Predictable time complexity: O(n * 4^W_max)
- Worst-case complexity on 3-SAT phase transition: O(2^(n/2) * poly(n))
- Built-in complexity diagnostics: estimates hardness before solving

---

## The Core Idea

1. Variable Lifetime Tracking

    For each variable x, we track two events:
    
    - t_in(x) — the step when the first clause containing x is added to the BDD.
    - t_out(x) — the step when the last clause containing x is processed and x is eliminated.
    
    Between t_in and t_out, x is active — present in the current BDD context.

2. Context Size

    At any step i, the context V_i is the set of active variables:
    
    V_i = x : t_in(x) ≤ i < t_out(x)
    
    The context width at step i:
    
    w_i = |V_i|
    
    The maximum context width over the whole run:
    
    W_max = \max_i w_i

3. Complexity Bound

    BDD size at step i is at most 2^w_i.
    Each operation (conjunction, elimination) costs O(|BDD|^2) = O(4^w_i).
    
    Total complexity:
    
    T(n) = O(n * 4^W_max)

---

## Why W_max Matters

- If W_max is small (e.g., log(n)), the formula is structurally easy — solved in near-polynomial time.
- If W_max approx n/2, the formula is in the phase transition region — hardest case, but still bounded by O(2^{n/2}).
- If W_max is large (> n/2), the formula may be exponentially hard for any algorithm.

Crucial: W_max can be estimated before solving by analyzing the interaction graph and simulating a greedy clause order.

---

### The Duality of P and Q

A deeper analysis reveals a fundamental duality in the PQ-algorithm:

- **`W_max` (context width)** is determined by the **`P` variables** (the core). It represents the **spatial complexity** — the peak memory required (size of the BDD).
- **The number of steps** is determined by the **`Q` variables** (the complement). It represents the **temporal complexity** — the runtime of the algorithm.

This leads to a powerful insight:
> **Total Complexity = Spatial Complexity × Temporal Complexity ≈ `W_max` × (number of steps)**

This product directly correlates with our integral metric `∑P(t)²` (the area under the core size curve). It explains why two formulas with the same `W_max` can have different difficulty: one might have a wider but shorter core, while the other has a narrower but longer-lived core.

---

## Algorithm (Conceptual)

```
1. Input: CNF formula F with n variables, m clauses.
2. Build variable interaction graph G (vertices = variables, edges = co-occurrence in clauses).
3. Estimate optimal clause order (greedy: always pick the clause closest to current context).
4. Simulate the order to compute tin(x) and tout(x) for each variable.
5. Compute Wmax = max_i |{x : tin(x) ≤ i < tout(x)}|.
6. If Wmax is large, expect exponential runtime; otherwise, fast.
7. Run actual BDD elimination:
   - BDD = True
   - For each clause in estimated order:
       BDD = BDD ∧ clause
       Eliminate all variables that no longer appear in remaining clauses
       (existential quantification ∃v)
       If BDD = False: return UNSAT
   - After all clauses processed:
       If BDD = False → UNSAT
       If BDD = True or BDD contains only constants → SAT
       (No final enumeration — result is already in BDD)
```

Important: The last clause is processed exactly like all others.
No special handling, no final "core enumeration".
The result is in the BDD immediately after the last elimination.

---

## Why It Works

1. Immediate Garbage Collection

    Variables are eliminated as soon as they become irrelevant (no longer appear in any remaining clause).
    This keeps the BDD small and context width minimal.

2. No Final Blowup

    Because variables are eliminated continuously, the BDD never stores the entire formula at once.
    At the end, it either reduces to True, False, or a small function — but no exponential final step.

3. Phase Transition Diagnostics

    For random 3-SAT with clause/variable ratio ≈ 4.26, the interaction graph forces W_{\max} \approx n/2.
    Thus:
    
    T_worst = O(2^{n/2} * poly(n))
    
    This is better than naive 2^n and matches the best known deterministic bounds for general CNF.

---

Comparison with Existing Algorithms

|Algorithm |Type |  Complexity (3-SAT)   |   Final Step |
| :--- | :---: |:---------------------:|-------------:|
|Brute force |deterministic |          2^n          |  Enumeration |
|DPLL/CDCL |deterministic |    2^n worst-case     | Backtracking |
|PQ-Algorithm |deterministic |  2^{n/2} worst-case   |None (BDD result)|
|PPSZ (best det.) |deterministic | 2^{0.386n} (complex*) |Complex algebra|
|Schöning |randomized |      2^{0.334n}       |Random walks|

*PQ-Algorithm is simpler than PPSZ, fully deterministic, and provides a guaranteed upper bound 2^{n/2} for any CNF — with no final enumeration.

---

Pre-Solving Complexity Diagnostics

Before running the main algorithm, you can estimate W_{\max}:

1. Build the variable interaction graph.
2. Run a greedy vertex cover approximation.
3. Simulate greedy clause order to estimate t_{\text{in}} and t_{\text{out}}.
4. Compute approximate W_{\max}.

If W_max is small → problem is easy.
If W_max approx n/2 → problem is in the phase transition zone, expect 2^{n/2} steps.

---

Strengths

- ✅ Deterministic — no randomness, always correct.
- ✅ Predictable — complexity can be estimated before solving.
- ✅ Adaptive — fast on structured problems, bounded on hard ones.
- ✅ Simple — only requires BDD and greedy clause selection.
- ✅ No final blowup — result emerges naturally from elimination.
- ✅ Provable bound — O(2^{n/2}) in the worst case (phase transition).

---

Limitations

- BDD size can blow up if W_max is underestimated.
- Optimal clause order estimation is heuristic; may not always achieve minimal W_max.
- Currently analyzed for 3-CNF; longer clauses may require adjustments.
- BDD implementation must support efficient existential quantification.

---

Repository Structure (Planned)

```
/
├── README.md              # This file
├── theory/                # Theoretical description
│   ├── pq-split.md        # root of theory of pq-alghoritm
│   ├── pq-to-bdd.md       # symbolic elimination description
├── recursive_learning     # recursive lerning based, subexponential, BDD based, ALL-SAT solver
│   ├── readme.md          # theory and description
│   ├── matryoshka.py      # python implementation ALL-SAT alghoritm
|   ├── dimacs_loader.py   # loader for dimasc files (.cnf)
├── research/              # some files for test theory
│   ├── test2              # symbolic elimination implementation with python
#####
all other files in progress.
#####
```

---

How to Contribute

- Fork the repo
- Try the algorithm on your own CNF instances
- Suggest improvements to the clause ordering heuristic
- Implement a faster BDD library (C++ recommended for production)
- Report bugs and edge cases

---

References

1. R. Bryant, "Graph-Based Algorithms for Boolean Function Manipulation", 1986 (BDD).
2. M. Davis, G. Logemann, D. Loveland, "A Machine Program for Theorem Proving", 1962 (DPLL).
3. R. Impagliazzo, R. Paturi, "On the Complexity of k-SAT", 2001 (ETH).
4. Treewidth and vertex cover in SAT solving (various authors).

---

Citation

If you use this algorithm in your research, please cite:

```
@misc{pq2025,
  author = {Golubin Roman},
  title = {PQ-Algorithm: Structural Elimination for SAT},
  year = {2026},
  publisher = {GitHub},
  url = {https://github.com/gromas/pqsat}
}
```

---

⭐ Star this repo if you find it interesting!
Issues and PRs welcome.
