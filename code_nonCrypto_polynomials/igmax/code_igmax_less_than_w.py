from imaxhs import Solver
import numpy as np
from sympy import symbols, Poly

import time
import psutil
import os
import tracemalloc


# wall time, cpu, mem
def run_and_measure_once_py(f, *args, **kw):
    p = psutil.Process(os.getpid())

    cpu0 = p.cpu_times()
    t0 = time.perf_counter()
    tracemalloc.start()

    out = f(*args, **kw)

    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    t1 = time.perf_counter()
    cpu1 = p.cpu_times()

    return {
        "result": out,
        "wall_time_s": t1 - t0,
        "cpu_time_s": (cpu1.user - cpu0.user) + (cpu1.system - cpu0.system),
        "peak_mem_MiB": peak / (1024 ** 2),
    }


# reading p list from file
def read_p(file):
    list = []
    with open(file, 'r') as f:
        for line in f:
            s = line.strip()
            inner = s[1:-1].strip()
            sublist = [int(elem) for elem in inner.split(',')]
            list.append(sublist)
    return list


def hamming_weight(lst):
    return int(sum(lst))


# solver helpers
def add_hard_clause(s: Solver, clause):
    """
    we have two options: add_clause(clause) and add_clause(clause, is_hard=True).
    """
    try:
        s.add_clause(clause)
    except TypeError:
        s.add_clause(clause, True)


def solve_with_assumptions(s: Solver, assumptions):
    try:
        return s.solve(assumptions)
    except TypeError:
        return s.solve()


# XOR in CNF
def add_xor2_cnf(s: Solver, out_lit: int, a: int, b: int):
    """
    out_lit <=> (a XOR b) in CNF with 4 clauses.
    """
    add_hard_clause(s, [-a, -b, -out_lit])
    add_hard_clause(s, [a, b, -out_lit])
    add_hard_clause(s, [a, -b, out_lit])
    add_hard_clause(s, [-a, b, out_lit])


def add_xor_equivalence(s: Solver, z: int, terms: list[int], next_var: int) -> int:
    """
    Add z == XOR(terms) using add_xor2_cnf function.
    Return: updated next_var.
    """
    if not terms:
        add_hard_clause(s, [-z])
        return next_var

    if len(terms) == 1:
        t = terms[0]
        add_hard_clause(s, [-z, t])
        add_hard_clause(s, [z, -t])
        return next_var

    y = next_var
    next_var += 1
    add_xor2_cnf(s, y, terms[0], terms[1])

    for t in terms[2:]:
        y2 = next_var
        next_var += 1
        add_xor2_cnf(s, y2, y, t)
        y = y2

    add_hard_clause(s, [-z, y])
    add_hard_clause(s, [z, -y])
    return next_var


# AT MOST w
def add_atmost(s: Solver, lits: list[int], k: int, next_var: int) -> int:
    """
    Adds CNF for sum(lits) <= k
    Return: updated next_var.
    Idea:
        - We want sum (lits) to be <=w, where lits is z_vars for us, so hw(p*q)<=w
        - SAT doesn't know comparisons like "at most" etc -> so we have to work with boolean variables, or clauses, etc
        - Therefore we will use a Sinz-like construction to enforce this, using additional variables
    """

    # trivial cases
    n = len(lits)
    if k >= n:
        return next_var
    if k < 0:
        add_hard_clause(s, [])  # UNSAT
        return next_var

    # additional variables
    svars = [[0] * (k + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        for j in range(1, k + 1):
            svars[i][j] = next_var
            next_var += 1

    # (-x1 v s[1,1]) - we want at least 1 (>=1)
    add_hard_clause(s, [-lits[0], svars[1][1]])

    # we use the idea of Sequential Counter and the fact that
    # s[i][j] = in the first i variables, there are at least j true
    for i in range(2, n + 1):
        xi = lits[i - 1]

        add_hard_clause(s, [-xi, svars[i][1]])
        add_hard_clause(s, [-svars[i - 1][1], svars[i][1]])
        add_hard_clause(s, [-xi, -svars[i - 1][k]])

        for j in range(2, k + 1):
            add_hard_clause(s, [-svars[i - 1][j], svars[i][j]])
            add_hard_clause(s, [-xi, -svars[i - 1][j - 1], svars[i][j]])

    return next_var


# padding with zero s.t. the list of coeffs for q will be of length t+1 (maximum degree t)
def pad_with_zeros(P_coeffs, target_len):
    if len(P_coeffs) > target_len + 1:
        raise ValueError("The list is longer than target_len.")
    return P_coeffs + [0] * (target_len + 1 - len(P_coeffs))


# find Q such that 1 <= weight(P*Q) <= w
def find_polynomial_Q(P_coeffs, t, d, w):
    """
    Find Q(x) with degree d such that 1 <= wt(P*Q) <= w.
    """
    x = symbols('x')

    # Build P in GF(2)
    P_coeffs = pad_with_zeros(P_coeffs, t)
    P_expr = sum(int(coef) * x ** i for i, coef in enumerate(P_coeffs))
    P = Poly(P_expr, x, modulus=2)

    solver = Solver()

    # q_j vars: 1..d+1  (q_0..q_d)
    q_vars = list(range(1, d + 2))
    # z_k vars: d+2 .. d+2+(t+d)  (z_0..z_{t+d})
    z_vars = list(range(d + 2, d + 2 + (t + d + 1)))

    # set q_d = 1
    add_hard_clause(solver, [q_vars[d]])

    max_deg = t + d
    assert len(z_vars) == max_deg + 1

    next_var = z_vars[-1] + 1

    # z_k = XOR of selected q_j based on P coefficients
    for k in range(max_deg + 1):
        terms = []
        for i in range(t + 1):
            if int(P_coeffs[i]) != 1:
                continue
            j = k - i
            if 0 <= j <= d:
                terms.append(q_vars[j])

        next_var = add_xor_equivalence(solver, z_vars[k], terms, next_var)

    # set: wt(z_vars) <= w   (hard)
    next_var = add_atmost(solver, z_vars, w, next_var)

    # set: wt(z_vars) >= 1   (hard)  => (z0 OR z1 OR ... OR z_{t+d})
    add_hard_clause(solver, z_vars)

    res = solve_with_assumptions(solver, [])
    if res not in (20, 30):
        return P, None, None, None

    optimum = ""
    match res:
        case 20:
            optimum = "s SATISFIABLE (non-optimal solution found)"
        case 30:
            optimum = "s OPTIMUM FOUND"
        case 10:
            optimum = "s UNSATISFIABLE"
        case 0:
            optimum = "s UNKNOWN"

    model = solver.get_model()
    q_vals = [1 if model[q_vars[j] - 1] > 0 else 0 for j in range(d + 1)]

    Q_expr = sum(int(coef) * x ** i for i, coef in enumerate(q_vals))
    Q = Poly(Q_expr, x, modulus=2)

    PQ = P * Q
    v = np.array(list(reversed(PQ.all_coeffs())), dtype=int)
    wt = hamming_weight(v)

    return P, q_vals, PQ, wt, optimum


if __name__ == "__main__":
    t = 50  # Degree of P
    d = 10  # Degree of Q
    w = 8  # Upper bound: wt(P*Q) <= w, and also wt(P*Q) >= 1

    print("t,d,w =", t, d, w)

    # path for input
    list_p = read_p("")

    q_out = []
    pq_out = []
    weigth_out= []
    peakmem = []
    cpu = []
    wall = []
    optimum = []

    for poz, pcoeffs in enumerate(list_p):
        print("p[{}] =".format(poz), pcoeffs)

        stats = run_and_measure_once_py(find_polynomial_Q, P_coeffs=pcoeffs, t=t, d=d, w=w)
        P, q_vals, PQ, wt, optim = stats["result"]

        print("Q =", q_vals)
        print("weight(PQ) =", wt)

        q_out.append(q_vals)
        pq_out.append(PQ)
        (weigth_out.append(wt))
        optimum.append(optim)

        peakmem.append(stats["peak_mem_MiB"])
        wall.append(stats["wall_time_s"])
        cpu.append(stats["cpu_time_s"])
    
    # path for output
    outdir = ""

    os.makedirs(outdir, exist_ok=True)

    with open(os.path.join(outdir, "result_q.txt"), "w") as f:
        for elem in q_out:
            f.write(f"{elem}\n")

    with (open(os.path.join(outdir, "pq_norm.txt"), "w") as f):
        for elem in weigth_out:
            f.write(f"{elem}\n")

    with open(os.path.join(outdir, "result_pq.txt"), "w") as f:
        for elem in pq_out:
            f.write(f"{elem}\n")

    with open(os.path.join(outdir, "wall_time.txt"), "w") as f:
        for elem in wall:
            f.write(f"{elem}\n")

    with open(os.path.join(outdir, "cpu_time.txt"), "w") as f:
        for elem in cpu:
            f.write(f"{elem}\n")

    with open(os.path.join(outdir, "peak_mem.txt"), "w") as f:
        for elem in peakmem:
            f.write(f"{elem}\n")

    with open(os.path.join(outdir, "optim.txt"), "w") as f:
        for elem in optimum:
            f.write(f"{elem}\n")

    print("---------------------------------")
    print("weight =", weigth_out)
    print("q =", q_out)
