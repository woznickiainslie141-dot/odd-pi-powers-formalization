"""Scan the two-level family nu = (a, b,...,b [T times], 0,...) for E_k.

Uses one exact partition for offsets 0..Tmax (zero weights are exact:
the larger partition refines every sub-partition).  Float search only.
usage: python scan_family.py k L Tmax amax bmax
"""
import sys
import math
import numpy as np
from scipy.optimize import brentq
from fast_eval import cell_data, THETA


def main(k, L, Tmax, amax, bmax):
    offs = tuple(range(Tmax + 1))
    ws, mats = cell_data(L, offs)
    c = np.array([1 - 2 * t / L for t in offs])
    best = []
    for T in range(1, Tmax + 1):
        for b in range(1, bmax + 1):
            a_vals = np.arange(1, amax + 1)
            NU = np.zeros((Tmax + 1, len(a_vals)))
            NU[0] = a_vals
            NU[1:T + 1] = b
            g = sum(w * (A @ NU).min(axis=0) for w, A in zip(ws, mats))
            for col, a in enumerate(a_vals):
                nu = NU[:, col]
                M = nu.sum(); m = M - 1
                eq = lambda Y: 2 * np.sum(nu * np.arctan(c / (2 * Y))) - THETA
                Y = brentq(eq, 0.5, 4 * M + 10, xtol=1e-13)
                Fc = c / 2 * np.log((1 + (2 * Y / c) ** 2) / 4) + 2 * Y * np.arctan(c / (2 * Y))
                D = np.sum(nu * Fc) - THETA * Y - m + g[col]
                G = m + np.sum(nu * c) * math.log(2) - g[col]
                gap = D - (k - 1) * G
                if G >= 0 and gap > 0:
                    best.append((m * (D + G) / gap, a, b, T, int(m)))
    best.sort()
    print(f"k={k} L={L} Tmax={Tmax}: top 8")
    for row in best[:8]:
        print("  E=%.4f a=%d b=%d T=%d m=%d" % row)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:6]))
