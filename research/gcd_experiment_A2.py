"""Experiment A2: where does the Gaussian-integer gcd exceed the integer gcd?
Decompose g_G / g_poly (g_G = Gaussian gcd of row evaluations at x=i)."""
from math import gcd, log
import sympy as sp
from audit_nested_pade import coefficients, evaluate_i, gcd_g
from gcd_experiment_A import intervals_for


def gauss_div(a, d):
    """exact Gaussian division a/d, assumed divisible"""
    nrm = d[0] ** 2 + d[1] ** 2
    re = a[0] * d[0] + a[1] * d[1]
    im = a[1] * d[0] - a[0] * d[1]
    assert re % nrm == 0 and im % nrm == 0
    return re // nrm, im // nrm


def main(L, offsets, counts, ns):
    for n in ns:
        iv = intervals_for(L, n, offsets, counts)
        m = sum(counts) - 1
        A = coefficients(m, n, iv)
        best = None
        for h in range(m + 1):
            g = 0
            for col in A[h]:
                for v in col:
                    g = gcd(g, int(v))
            gg = (0, 0)
            for col in A[h]:
                gg = gcd_g(gg, evaluate_i([int(v) for v in col], n))
            if best is None or g < best[0]:
                best = (g, gg, h)
        g, gg, h = best
        quo = gauss_div(gg, (g, 0))
        N = quo[0] ** 2 + quo[1] ** 2
        fac = sp.factorint(N)
        two = fac.pop(2, 0)          # (1+i)-adic part (norm 2 each)
        split = {p: e for p, e in fac.items() if p % 4 == 1}
        inert = {p: e for p, e in fac.items() if p % 4 == 3}
        print(f"L={L} cnt={counts} n={n} row={h} "
              f"log|g_poly|/n={log(g)/n:.3f} "
              f"(1+i)-part={two*0.5*log(2)/n:.3f} "
              f"split-part={sum(e*0.5*log(p) for p,e in split.items())/n:.3f} "
              f"inert-part={sum(e*0.5*log(p) for p,e in inert.items())/n:.3f}"
              f" split={split}", flush=True)


if __name__ == "__main__":
    main(6, (0, 1), (2, 2), [30, 42, 54, 66, 78])
    main(9, (0, 1, 2), (2, 1, 1), [45, 63, 81, 99])
