"""Fast float evaluator for the nested-interval bound E_k (search only).

Exact arc partition (Fractions, same algorithm as code/certify.py), float
digamma weights, float saddle root.  Results are NOT certificates: any
candidate must be re-certified with code/certify.py's Arb routine.
"""
from fractions import Fraction as F
from functools import lru_cache
import math
import numpy as np
from scipy.special import digamma
from scipy.optimize import brentq

THETA = math.pi / 2


def _floor(q):
    return q.numerator // q.denominator


@lru_cache(None)
def arc_partition(L, offsets):
    """Cells (a, b, rows) with rows = all distinct W-vectors on the cell."""
    slopes = sorted({0, *offsets, *(L - t for t in offsets)})
    diffs = {abs(a - b) for a in slopes for b in slopes if a != b}
    cuts = sorted({F(k, d) for d in diffs for k in range(d + 1)})
    cells = []
    for a, b in zip(cuts, cuts[1:]):
        z = (a + b) / 2
        ends = sorted({F(0), F(1), *((t * z) % 1 for t in slopes)})
        rows = set()
        for u, v in zip(ends, ends[1:]):
            y = (u + v) / 2
            row = tuple(_floor((L - 2 * t) * z) - _floor(y - t * z)
                        - _floor((L - t) * z - y) for t in offsets)
            rows.add(row)
        cells.append((a, b, tuple(sorted(rows))))
    return tuple(cells)


@lru_cache(None)
def cell_data(L, offsets):
    """(weights w_cell, list of row matrices) with w=(psi(b)-psi(a))/L.

    Cells containing the all-zero row (common point) have f=0 for every
    weight vector and are dropped; the cell at a=0 is always such a cell.
    """
    ws, mats = [], []
    for a, b, rows in arc_partition(L, offsets):
        if any(all(x == 0 for x in r) for r in rows):
            continue
        assert a > 0
        ws.append((digamma(float(b)) - digamma(float(a))) / L)
        mats.append(np.array(rows, dtype=float))
    return np.array(ws), mats


def gamma(L, offsets, nu):
    ws, mats = cell_data(L, tuple(offsets))
    nu = np.asarray(nu, dtype=float)
    return float(sum(w * (A @ nu).min() for w, A in zip(ws, mats)))


def rates(L, offsets, nu, g=None):
    nu = np.asarray(nu, dtype=float)
    c = np.array([1 - 2 * t / L for t in offsets])
    M = nu.sum()
    m = M - 1
    eq = lambda Y: 2 * np.sum(nu * np.arctan(c / (2 * Y))) - THETA
    Y = brentq(eq, 0.5, 4 * M + 10, xtol=1e-14, rtol=1e-15)
    F_ = c / 2 * np.log((1 + (2 * Y / c) ** 2) / 4) + 2 * Y * np.arctan(c / (2 * Y))
    D0 = float(np.sum(nu * F_) - THETA * Y - m)
    G0 = float(m + np.sum(nu * c) * math.log(2))
    if g is None:
        g = gamma(L, offsets, nu)
    return dict(m=m, Y=Y, D0=D0, G0=G0, gamma=g, D=D0 + g, G=G0 - g)


def E(k, L, offsets, nu):
    r = rates(L, offsets, nu)
    gap = r["D"] - (k - 1) * r["G"]
    if r["G"] < 0 or gap <= 0:
        return math.inf
    return r["m"] * (r["D"] + r["G"]) / gap


def rho(L, offsets, v):
    """Growth constant of a scaled shape: rho = 2*exp((V-gamma)/S)."""
    v = np.asarray(v, dtype=float)
    c = np.array([1 - 2 * t / L for t in offsets])
    V, S = v.sum(), float(np.sum(v * c))
    return 2 * math.exp((V - gamma(L, offsets, v)) / S)


if __name__ == "__main__":
    off = tuple(range(12))
    print("E3 twelve-layer:", E(3, 69, off, [66] + [11] * 11), "(expect 1203.9724)")
    print("gamma*:", gamma(69, off, [6] + [1] * 11), "(expect 4.1305456)")
    print("rho:", rho(69, off, [6] + [1] * 11), "(expect 4.6934399)")
    print("E5:", E(5, 69, off, [1554] + [259] * 11), "(expect 42460.70)")
    print("E3 two-layer:", E(3, 14, (0, 1), [128, 128]), "(expect 1762.608)")
