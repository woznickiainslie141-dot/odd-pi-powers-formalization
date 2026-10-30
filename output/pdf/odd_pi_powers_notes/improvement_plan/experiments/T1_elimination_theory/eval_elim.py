"""T1: float evaluation of elimination-variant exponents (search/diagnostics only).

theta = Theta (pi/2 for x=i, pi for x=-1).  gamma reused from ../fast_eval.py.
"""
import math, sys
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from fast_eval import gamma  # noqa: E402


def rates(L, offsets, nu, theta=math.pi / 2, g=None):
    nu = np.asarray(nu, dtype=float)
    c = np.array([1 - 2 * t / L for t in offsets])
    M = nu.sum(); m = M - 1
    eq = lambda Y: 2 * np.sum(nu * np.arctan(c / (2 * Y))) - theta
    Y = brentq(eq, 1e-9, 4 * M + 10, xtol=1e-14, rtol=1e-15)
    Fc = c / 2 * np.log((1 + (2 * Y / c) ** 2) / 4) + 2 * Y * np.arctan(c / (2 * Y))
    D0 = float(np.sum(nu * Fc) - theta * Y - m)
    G0 = float(m + np.sum(nu * c) * math.log(2))
    if g is None:
        g = gamma(L, tuple(offsets), list(nu)) if len(offsets) > 1 else 0.0
    return dict(m=int(m), Y=Y, D=D0 + g, G=G0 - g, gamma=g,
                Yok=bool(Y > 0.5))


def balanced(M, theta=math.pi / 2):
    m = M - 1
    D = -M * math.log(2 * math.sin(theta / (2 * M))) - m
    G = m + M * math.log(2)
    Y = 0.5 / math.tan(theta / (2 * M))
    return dict(m=m, D=D, G=G, gamma=0.0, Y=Y, Yok=Y > 0.5)


def E_res(k, r):          # original Thm 1.1
    gap = r["D"] - (k - 1) * r["G"]
    return math.inf if gap <= 0 else r["m"] * (r["D"] + r["G"]) / gap


def E_A(k, r):            # Theorem A (worst case of elimination)
    gap = r["D"] - (k - 1) * r["G"]
    return math.inf if gap <= 0 else (r["m"] + 1 - k) * (r["D"] + r["G"]) / gap


def E_bal(k, r, exact=True):  # heuristic balanced-minima exponent
    m = r["m"]; d = m + 2 - k; rp = (k - 1) / d
    gap = r["D"] - rp * r["G"]
    if gap <= 0:
        return math.inf
    if exact:
        d0 = m // k; sig = m + 1 - k - d0
        pre = d0 + sig / d
    else:
        pre = m * (1 + rp) / k
    return pre * (r["D"] + r["G"]) / gap


def E_free2(r):           # k=2 at x=-1 via P_odd: floor((m-1)/2)(D+G)/D
    return math.inf if r["D"] <= 0 else ((r["m"] - 1) // 2) * (r["D"] + r["G"]) / r["D"]


def E_k1(r):              # k=1: m(D+G)/D
    return math.inf if r["D"] <= 0 else r["m"] * (r["D"] + r["G"]) / r["D"]


if __name__ == "__main__":
    tw = rates(69, tuple(range(12)), [66] + [11] * 11)
    print("12-layer k=3: res", E_res(3, tw), "A", E_A(3, tw),
          "bal_exact", E_bal(3, tw), "bal_doc", E_bal(3, tw, False))
    l99 = rates(99, tuple(range(28)), [64] + [4] * 27)
    print("L99 k=3: res", E_res(3, l99), "A", E_A(3, l99), "bal", E_bal(3, l99))
    print("balanced m=289 k=3: res", E_res(3, balanced(290)), "A", E_A(3, balanced(290)))
    # k=1 balanced at x=i
    best = min((E_k1(balanced(M)), M) for M in range(2, 80))
    print("k=1 balanced x=i best (E,M):", best)
    for M in (5, 6, 7, 8):
        print("  M", M, E_k1(balanced(M)))
    # k=3 balanced-heuristic over balanced intervals
    bb = min((E_bal(3, balanced(M)), M) for M in range(4, 80))
    bd = min((E_bal(3, balanced(M), False), M) for M in range(4, 80))
    print("k=3 balanced intervals, E_bal exact best:", bb, " doc-formula best:", bd)
    # k=2 at x=-1 balanced
    b2 = min((E_free2(balanced(M, math.pi)), M) for M in range(3, 80))
    b2e = min((((M - 1) // 2) * 0 + E_free2(balanced(M, math.pi)), M)
              for M in range(3, 80) if (M - 1) % 2 == 1)
    print("k=2 x=-1 balanced best:", b2, "(odd m only:", b2e, ")")
    for M in range(3, 12):
        r = balanced(M, math.pi)
        print("  M", M, "m", r["m"], "D", round(r["D"], 4), "G", round(r["G"], 4),
              "E", E_free2(r), "even-part version",
              (r["m"] // 2) * (r["D"] + r["G"]) / r["D"] if r["D"] > 0 else None)
