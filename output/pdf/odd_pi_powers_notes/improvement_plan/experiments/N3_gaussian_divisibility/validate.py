"""Validate gauss_div.coeff_matrix against code/finite_checks.py and the toy matrix."""
import sys, time
from pathlib import Path
import sympy as sp
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "code"))
import finite_checks as fc
from gauss_div import *

x = sp.Symbol("x")
for m, n, intervals in [(1, 4, [(0, 4), (1, 3)]), (2, 6, [(0, 6), (0, 6), (1, 5)]),
                        (3, 8, [(0, 8), (1, 7), (1, 7), (2, 6)]),
                        (4, 12, [(0, 12), (0, 12), (2, 10), (3, 9), (3, 9)])]:
    groups = []
    for a, b in intervals:
        if groups and groups[-1][0] == a:
            groups[-1] = (a, b, groups[-1][2] + 1)
        else:
            groups.append((a, b, 1))
    A = coeff_matrix(n, groups)
    ref = fc.coefficients(m, n, intervals)
    ok = all(int(ref[h][j][l]) == A[h][j][l] and ref[h][j][l].denominator == 1
             for h in range(m + 1) for j in range(m + 1) for l in range(n + 1))
    mat = sp.Matrix([[sum(A[h][j][l] * x ** (n - l) for l in range(n + 1))
                      for j in range(m + 1)] for h in range(m + 1)])
    det = sp.factor(mat.det())
    N = sum(b - a for a, b in intervals)
    off = sum(n - b for a, b in intervals)
    cn = sp.cancel(det / (x ** off * (x - 1) ** N))
    lead = [[A[h][j][intervals[j][0]] for j in range(m + 1)] for h in range(m + 1)]
    cn2 = bareiss_int(lead)
    Ai = [[eval_at_i(A[h][j], n) for j in range(m + 1)] for h in range(m + 1)]
    di = bareiss_gauss(Ai)
    pred = gmul((int(cn2), 0), gmul(gpow((0, 1), off), gpow((-1, 1), N)))
    print(m, n, "match finite_checks:", ok, "| det =", det, "| c_n(sympy)=", cn,
          "| c_n(lead det)=", cn2, "| det(A(i)) check:", di == pred)
    if m == 1:
        print("  toy matrix:", mat)
