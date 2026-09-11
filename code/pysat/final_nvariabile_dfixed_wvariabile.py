from pysat.card import CardEnc
from pysat.solvers import Solver
from sympy import symbols, Poly
import time, psutil
from memory_profiler import memory_usage
import os
from pysat.formula import CNF
from random import seed


def pad_with_zeros(P_coeffs, target_len):
    if len(P_coeffs) > target_len+1:
        raise ValueError("The list is longer than target_len.")
    return P_coeffs + [0] * (target_len + 1 - len(P_coeffs))


def run_and_measure_once(f, *args, **kw):
    p = psutil.Process(os.getpid())

    cpu0 = p.cpu_times()
    t0 = time.perf_counter()

    mem, out = memory_usage(
        (f, args, kw),
        interval=0.05,
        max_iterations=1,
        retval=True
    )

    t1 = time.perf_counter()
    cpu1 = p.cpu_times()

    return {
        "result": out,
        "wall_time_s": t1 - t0,
        "cpu_time_s": (cpu1.user - cpu0.user) + (cpu1.system - cpu0.system),
        "peak_mem_MiB": max(mem)
    }


def read_P_file(p_path: str) -> list[list[int]]:
    P_list = []
    with open(p_path, "r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, start=1):
            s = line.strip()
            if not s:
                continue

            if not (s.startswith("[") and s.endswith("]")):
                raise ValueError(f"Line {line_no}: invalid format")

            inner = s[1:-1].strip()

            if inner == "":
                P_list.append([])
                continue

            try:
                P_vec = [int(x.strip()) for x in inner.split(",")]
            except ValueError:
                raise ValueError(f"Line {line_no}: invalid format")

            P_list.append(P_vec)

    return P_list


def find_polynomial_Q(P_coeffs, t, d, w, verbose=True):
    x = symbols('x')

    if len(P_coeffs) > t + 1:
        raise ValueError(f"len(P_coeffs)={len(P_coeffs)}, but we need t+1={t + 1}")

    P_expr = sum(int(coef) * x ** i for i, coef in enumerate(P_coeffs))
    P = Poly(P_expr, x, modulus=2)
    print("P(x):", P)

    q_vars = list(range(1, d + 2))  # q_0..q_d
    z_vars = list(range(d + 2, d + 2 + (t + d + 1)))  # z_0..z_{t+d}

    max_deg = t + d

    with Solver(name='cms', bootstrap_with=[]) as s:
        # XOR: z_k = sum_{i+j=k} p_i * q_j mod 2
        for k in range(max_deg + 1):
            terms = []
            for i in range(t + 1):
                j = k - i
                if 0 <= j <= d and P_coeffs[i] == 1:
                    terms.append(q_vars[j])

            if terms:
                # z_k = XOR(terms)
                s.add_xor_clause(lits=[z_vars[k]] + terms, value=False)
            else:
                # z_k = 0
                s.add_clause([-z_vars[k]])

        # optional: degree(Q) exactly d
        s.add_clause([q_vars[d]])

        # condition: norm(PQ) <= w
        s.append_formula(CardEnc.atmost(lits=z_vars, bound=w, encoding=1).clauses)
        s.append_formula(CardEnc.atleast(lits=z_vars, bound=1, encoding=1).clauses)

        # solve
        if not s.solve():
            if verbose:
                print("UNSAT (there is no Q with norm(PQ) <= w for this P)")
            return None, None, None, "UNSAT"

        model = s.get_model()

        # extract Q from model
        q_coeffs = [1 if model[v - 1] > 0 else 0 for v in q_vars]
        q_list = [int(model[q_vars[j] - 1] > 0) for j in range(d + 1)]
        print("q list:", q_list)

        z_weight_model = sum(1 for z in z_vars if model[z - 1] > 0)

        # compute PQ and norm
        Q_expr = sum(coef * x ** i for i, coef in enumerate(q_coeffs))
        Q = Poly(Q_expr, x, modulus=2)
        print("q:", Q)
        PQ = (P * Q).set_modulus(2)
        pq_coeffs = PQ.all_coeffs()
        print("pq:", pq_coeffs)

        pq_coeffs_sympy = [int(c) & 1 for c in PQ.all_coeffs()]
        pq_weight_sympy = sum(pq_coeffs_sympy)

        if verbose:
            print("SAT")
            print("weight(PQ) from model =", z_weight_model, " (w =", w, ")")
            print("weight(PQ) sympy     =", pq_weight_sympy)

        return q_list, pq_coeffs, pq_weight_sympy, "SAT"


if __name__ == '__main__':

    in_dir = r""

    # input
    p_path = os.path.join(in_dir, "coeffs_p.txt")

    out_dir = r""

    os.makedirs(out_dir, exist_ok=True)


    N = 250
    t = 400  # Degree of P
    d = 100  # Degree of Q
    w = 10 # Max Hamming weight
    # weightP = 7

    P_all = read_P_file(p_path)
    print(P_all)
    with \
            open(os.path.join(out_dir, "q.txt"), "w", encoding="utf-8") as f_Q, \
            open(os.path.join(out_dir, "pq.txt"), "w", encoding="utf-8") as f_PQ, \
            open(os.path.join(out_dir, "pq_norm.txt"), "w", encoding="utf-8") as f_norm, \
            open(os.path.join(out_dir, "wall_time.txt"), "w", encoding="utf-8") as f_wall, \
            open(os.path.join(out_dir, "cpu_time.txt"), "w", encoding="utf-8") as f_cpu, \
            open(os.path.join(out_dir, "peak_mem.txt"), "w", encoding="utf-8") as f_mem:

        for i, P_coeffs in enumerate(P_all):
            print(f"Instance {i + 1}/{len(P_all)}")
            seed(i)
            P_coeffs = pad_with_zeros(P_coeffs, t)
            print(find_polynomial_Q(P_coeffs=P_coeffs, t=t, d=d, w=w))

            try:
                stats = run_and_measure_once(
                    find_polynomial_Q,
                    P_coeffs=P_coeffs, t=t, d=d, w=w,
                    verbose=False
                )
            except Exception as e:
                print(e)
                print("Solver error, skipping instance", i)
                continue

            Q, PQ, pq_norm, info = stats["result"]

            print(Q, type(Q))
            print(PQ)
            print(info)
            if info != "SAT":
                print("no feasible solution, skipping", i + 1)
                Q_vec = [0]
                PQ_vec = [0]
                pq_norm = 0

                f_wall.write(f"{stats['wall_time_s']}\n")
                f_cpu.write(f"{stats['cpu_time_s']}\n")
                f_mem.write(f"{stats['peak_mem_MiB']}\n")

                f_Q.write(str(Q_vec) + "\n")
                f_PQ.write(str(PQ_vec) + "\n")
                f_norm.write(str(pq_norm) + "\n")
                continue

            f_wall.write(f"{stats['wall_time_s']}\n")
            f_cpu.write(f"{stats['cpu_time_s']}\n")
            f_mem.write(f"{stats['peak_mem_MiB']}\n")

            f_Q.write(str(Q) + "\n")
            f_PQ.write(str(PQ) + "\n")
            f_norm.write(str(pq_norm) + "\n")
