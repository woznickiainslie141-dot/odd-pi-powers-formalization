"""Global minimum of rho = 2 exp((V - gamma)/S) over weight shapes, fixed L.

gamma(v) = sum_cell w_cell * min_row(row . v) is concave piecewise linear,
so with the normalisation S = sum v_t c_t = 1 (Charnes-Cooper) the problem
  minimise  sum_t v_t - sum_cell w_cell g_cell
  s.t.      g_cell <= row . v  (every row of every cell),  v >= 0,  S = 1
is an exact LP.  Offsets range over a candidate set; zero weights drop out.
Search tool only: re-certify any rational shape with code/certify.py.
"""
import sys
import math
import time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix
from fast_eval import cell_data, rho


def solve(L, offsets, v0_min=1e-6):
    offsets = tuple(offsets)
    ws, mats = cell_data(L, offsets)
    T, C = len(offsets), len(ws)
    c_len = np.array([1 - 2 * t / L for t in offsets])
    nrows = sum(A.shape[0] for A in mats)
    # variables: v (T), g (C)
    A = lil_matrix((nrows, T + C))
    r = 0
    for j, Aj in enumerate(mats):
        for row in Aj:
            A[r, :T] = -row
            A[r, T + j] = 1.0
            r += 1
    cost = np.concatenate([np.ones(T), -ws])
    Aeq = np.concatenate([c_len, np.zeros(C)])[None, :]
    bounds = [(v0_min, None)] + [(0, None)] * (T - 1) + [(None, None)] * C
    res = linprog(cost, A_ub=csr_matrix(A), b_ub=np.zeros(nrows),
                  A_eq=Aeq, b_eq=[1.0], bounds=bounds, method="highs")
    assert res.status == 0, res.message
    v = res.x[:T]
    return 2 * math.exp(res.fun), v


if __name__ == "__main__":
    for L in map(int, sys.argv[1:] or ["69"]):
        offs = tuple(range((L - 1) // 2 + 1))
        t0 = time.time()
        r, v = solve(L, offs)
        keep = [(t, x / v[0]) for t, x in zip(offs, v) if x > 1e-9 * v.max()]
        chk = rho(L, [t for t, _ in keep], [x for _, x in keep])
        print(f"L={L} rho_LP={r:.6f} check={chk:.6f} "
              f"support={len(keep)} time={time.time()-t0:.1f}s")
        print("  shape (t, v_t/v_0):",
              ", ".join(f"{t}:{x:.4f}" for t, x in keep))
