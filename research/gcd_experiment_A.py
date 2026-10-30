"""Experiment A: true common divisor of the exact nested-Pade rows vs. the
proved floor-function divisor Pi_n.  Finite exact data only; it does not prove
any asymptotic rate.  Run from the research directory."""
from math import gcd, log, isqrt
from pathlib import Path
import json
import sys
import sympy as sp
from audit_nested_pade import coefficients, evaluate_i, gcd_g

OUT = Path(__file__).resolve().parent


def intervals_for(L, n, offsets, counts):
    out = []
    for t, c in zip(offsets, counts):
        out += [(t * n // L, (L - t) * n // L)] * c
    return out


def vp(x, p):
    x = abs(x)
    if x == 0:
        return 10**9
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def predicted_valuation(p, n, intervals):
    """Proved lower bound on v_p of every integer polynomial coefficient."""
    return min(sum((b - a) // p - (l - a) // p - (b - l) // p
                   for a, b in intervals) for l in range(n + 1))


def run(L, offsets, counts, n):
    iv = intervals_for(L, n, offsets, counts)
    m = sum(counts) - 1
    A = coefficients(m, n, iv)
    primes = list(sp.primerange(2, n + 1))
    pred = {p: (predicted_valuation(p, n, iv) if p > isqrt(n) else 0)
            for p in primes}
    log_pred = sum(v * log(p) for p, v in pred.items())
    rows = []
    for h in range(m + 1):
        ints = [int(v) for col in A[h] for v in col]
        g = 0
        for v in ints:
            g = gcd(g, v)
        gg = (0, 0)
        for col in A[h]:
            gg = gcd_g(gg, evaluate_i([int(v) for v in col], n))
        normG = gg[0] ** 2 + gg[1] ** 2
        val = {p: vp(g, p) for p in primes}
        rows.append({"h": h, "log_polygcd": log(g) if g else None,
                     "log_gauss_abs": 0.5 * log(normG) if normG else None,
                     "val": val})
    # worst row = what a uniform divisor can use
    wp = min(r["log_polygcd"] for r in rows)
    wg = min(r["log_gauss_abs"] for r in rows)
    # excess valuation by prime class for the worst-poly row
    worst = min(rows, key=lambda r: r["log_polygcd"])
    cls = {"p<=sqrt n": 0.0, "sqrt n<p<=n/2": 0.0, "n/2<p<=n": 0.0}
    miss = []
    for p in primes:
        ex = worst["val"][p] - pred[p]
        if ex < 0:
            miss.append((p, ex))
        if p <= isqrt(n):
            k = "p<=sqrt n"
        elif p <= n // 2:
            k = "sqrt n<p<=n/2"
        else:
            k = "n/2<p<=n"
        cls[k] += max(ex, 0) * log(p)
    return {"L": L, "offsets": list(offsets), "counts": list(counts), "m": m,
            "n": n, "pred_rate": log_pred / n, "poly_rate": wp / n,
            "gauss_rate": wg / n,
            "excess_by_class_rate": {k: v / n for k, v in cls.items()},
            "bound_violations": miss}


CONFIGS = [
    # (L, offsets, counts, list of n)
    (1, (0,), (3,), [8, 16, 24, 32, 40]),                 # balanced m=2
    (1, (0,), (4,), [8, 16, 24, 32, 40]),                 # balanced m=3
    (6, (0, 1), (2, 2), [6, 12, 18, 24, 30, 36, 42]),
    (9, (0, 1, 2), (2, 1, 1), [9, 18, 27, 36, 45]),
    (14, (0, 1), (3, 3), [14, 28, 42, 56]),
]

if __name__ == "__main__":
    results = []
    for L, off, cnt, ns in CONFIGS:
        for n in ns:
            r = run(L, off, cnt, n)
            results.append(r)
            e = r["excess_by_class_rate"]
            print(f"L={L} off={off} cnt={cnt} m={r['m']} n={n:3d} "
                  f"pred={r['pred_rate']:.3f} poly={r['poly_rate']:.3f} "
                  f"gauss={r['gauss_rate']:.3f} | excess small={e['p<=sqrt n']:.3f} "
                  f"mid={e['sqrt n<p<=n/2']:.3f} top={e['n/2<p<=n']:.3f} "
                  f"viol={len(r['bound_violations'])}", flush=True)
    (OUT / "gcd_experiment_A_2026-10-27.json").write_text(
        json.dumps(results, indent=1), encoding="utf-8")
