from pysat.card import CardEnc
from pysat.solvers import Solver
from sympy import symbols, Poly
import time, psutil
from memory_profiler import memory_usage
import os
from pysat.formula import CNF
from random import seed
import multiprocessing as mp


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


def solver_worker(queue, kwargs):
    try:
        stats = run_and_measure_once(find_polynomial_Q, **kwargs)
        queue.put(("OK", stats))
    except Exception as e:
        queue.put(("ERROR", str(e)))


def run_with_timeout(timeout_s, **kwargs):
    queue = mp.Queue()

    p = mp.Process(
        target=solver_worker,
        args=(queue, kwargs)
    )

    p.start()
    p.join(timeout_s)

    if p.is_alive():
        p.terminate()
        p.join()
        return "TIMEOUT", None

    if queue.empty():
        return "ERROR", None

    status, data = queue.get()

    if status == "ERROR":
        print(data)
        return "ERROR", None

    return "OK", data


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
    p_path = os.path.join(in_dir, "didier.txt")

    out_dir = r""

    os.makedirs(out_dir, exist_ok=True)

    N = 1
    t =   # Degree of P
    d =   # Degree of Q
    w =  # Max Hamming weight
    # weightP = 7

    w_min = 1
    time_limit = 120.0

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

            search_start = time.perf_counter()

            best_Q = None
            best_PQ = None
            best_norm = None
            best_wall = None

            total_cpu = 0.0
            peak_mem = 0.0

            for current_w in range(w, w_min, -1):

                print("Trying w =", current_w)

                status, stats = run_with_timeout(
                    time_limit,
                    P_coeffs=P_coeffs,
                    t=t,
                    d=d,
                    w=current_w,
                    verbose=False
                )

                if status == "TIMEOUT":
                    print(f"TIMEOUT while testing w={current_w} after {time_limit:.2f}s.")
                    continue

                if status == "ERROR":
                    print("Solver error, skipping w =", current_w)
                    continue

                Q, PQ, pq_norm, info = stats["result"]

                total_cpu += stats["cpu_time_s"]
                peak_mem = max(peak_mem, stats["peak_mem_MiB"])

                elapsed = time.perf_counter() - search_start

                print(Q, type(Q))
                print(PQ)
                print(info)

                if info != "SAT":
                    print("no feasible solution for w =", current_w)
                    break

                if best_norm is None or pq_norm < best_norm:
                    best_Q = Q
                    best_PQ = PQ
                    best_norm = pq_norm
                    best_wall = elapsed

                if best_norm <= w_min:
                    break

            total_wall = time.perf_counter() - search_start

            if best_Q is None:
                best_Q = [0]
                best_PQ = [0]
                best_norm = 0
                best_wall = total_wall

            print("Best Q =", best_Q)
            print("Best PQ =", best_PQ)
            print("Best weight =", best_norm)
            print("Best wall-time =", best_wall)
            print("Total wall-time =", total_wall)

            f_wall.write(f"{best_wall}\n")
            f_cpu.write(f"{total_cpu}\n")
            f_mem.write(f"{peak_mem}\n")

            f_Q.write(str(best_Q) + "\n")
            f_PQ.write(str(best_PQ) + "\n")