"""Fast exact arc partition (integer arithmetic) + batched float evaluator.

Same cells and same W-vectors as code/certify.py::arc_partition, but every
fraction is handled as an integer numerator over a common denominator, and
rows are reduced to their componentwise-minimal set (dominated rows can never
attain min_rows <nu,row> for nu >= 0).  Cells with identical minimal-row sets
are merged (weights add).  Float search only; certificates use certify.py.
"""
from fractions import Fraction as Fr
from math import gcd
import math
import pickle
import time
from pathlib import Path
import numpy as np
from scipy.special import digamma

THETA = math.pi / 2
_MEM = {}  # in-memory cache only (disk cache removed: disk space)


def cuts_of(L, offsets):
    slopes = sorted({0, *offsets, *(L - t for t in offsets)})
    diffs = sorted({abs(a - b) for a in slopes for b in slopes if a != b})
    s = set()
    for d in diffs:
        for k in range(d + 1):
            g = gcd(k, d)
            s.add((k // g, d // g))
    cuts = sorted(s, key=lambda x: x[0] / x[1])
    return slopes, cuts


def minimal_rows(R):
    """Remove rows dominated (>= componentwise, not equal) by another row."""
    if len(R) <= 1:
        return R
    # sort by row sum so a dominating (smaller) row comes first
    R = R[np.argsort(R.sum(axis=1), kind="stable")]
    keep = []
    for i in range(len(R)):
        r = R[i]
        dom = False
        for j in keep:
            if np.all(R[j] <= r):
                dom = True
                break
        if not dom:
            keep.append(i)
    return R[keep]


def minimal_rows_fast(R):
    if len(R) <= 1:
        return R
    R = R[np.argsort(R.sum(axis=1), kind="stable")]
    # pairwise dominance: row j dominates row i if R[j] <= R[i] all, j != i
    le = np.all(R[:, None, :] <= R[None, :, :], axis=2)  # le[j,i]: R[j]<=R[i]
    np.fill_diagonal(le, False)
    # identical rows were removed by unique already, so le[j,i] & le[i,j] impossible
    dominated = le.any(axis=0)
    return R[~dominated]


def build(L, offsets, verbose=False):
    offsets = tuple(int(t) for t in offsets)
    if (L, offsets) in _MEM:
        return _MEM[(L, offsets)]
    t0 = time.time()
    slopes, cuts = cuts_of(L, offsets)
    sl = np.array(slopes, dtype=np.int64)
    off = np.array(offsets, dtype=np.int64)
    groups = {}
    ncell = 0
    zero_cells = 0
    for (p1, q1), (p2, q2) in zip(cuts, cuts[1:]):
        ncell += 1
        # z = (p1/q1 + p2/q2)/2 = P/Q
        P = p1 * q2 + p2 * q1
        Q = 2 * q1 * q2
        g = gcd(P, Q)
        P //= g
        Q //= g
        # fractional parts of t*z, as integers mod Q
        ends = np.unique(np.concatenate(([0, Q], (sl * P) % Q)))
        # midpoints y = (u+v)/2 over denominator 2Q
        ymid = ends[:-1] + ends[1:]  # numerator over 2Q
        D2 = 2 * Q
        A = (L - 2 * off) * P * 2  # numerator over 2Q of (L-2t)z
        Bt = off * P * 2           # t z over 2Q
        Ct = (L - off) * P * 2     # (L-t) z over 2Q
        # row[t] = floor((L-2t)z) - floor(y - t z) - floor((L-t)z - y)
        rows = (A[None, :] // D2
                - (ymid[:, None] - Bt[None, :]) // D2
                - (Ct[None, :] - ymid[:, None]) // D2)
        rows = np.unique(rows, axis=0)
        assert rows.min() >= 0 and rows.max() <= 1
        if (rows.sum(axis=1) == 0).any():
            zero_cells += 1
            continue
        assert p1 > 0
        rows = minimal_rows_fast(rows.astype(np.int8))
        w = (digamma(p2 / q2) - digamma(p1 / q1)) / L
        k = rows.tobytes() + bytes([rows.shape[0] & 255, rows.shape[0] >> 8])
        if k in groups:
            groups[k][1] += w
        else:
            groups[k] = [rows, w]
    mats = [v[0] for v in groups.values()]
    ws = np.array([v[1] for v in groups.values()])
    R = np.concatenate(mats).astype(np.float32)
    starts = np.cumsum([0] + [len(m) for m in mats[:-1]])
    data = dict(L=L, offsets=offsets, ws=ws, R=R, starts=starts,
                ncell=ncell, zero_cells=zero_cells, ngroups=len(mats),
                nrows=R.shape[0], secs=time.time() - t0)
    _MEM[(L, offsets)] = data
    if verbose:
        print(f"build L={L} n_off={len(offsets)}: cells={ncell} zero={zero_cells} "
              f"groups={len(mats)} rows={R.shape[0]} in {data['secs']:.1f}s", flush=True)
    return data


def gamma_batch(data, NU):
    """NU: (n_off, B) array of weights; returns gamma for each column."""
    NU = np.asarray(NU, dtype=np.float32)
    if NU.ndim == 1:
        NU = NU[:, None]
    V = data["R"] @ NU                      # (nrows, B)
    mins = np.minimum.reduceat(V, data["starts"], axis=0)  # (ngroups, B)
    return data["ws"] @ mins.astype(np.float64)


def rates_batch(L, offsets, NU, g):
    """Vectorized D0, G0, D, G, E-pieces for weights NU (n_off,B) and gamma g (B,)."""
    NU = np.asarray(NU, dtype=np.float64)
    if NU.ndim == 1:
        NU = NU[:, None]
    c = np.array([1 - 2 * t / L for t in offsets])[:, None]
    M = NU.sum(axis=0)
    m = M - 1
    S = (NU * c).sum(axis=0)
    Y = S / THETA  # upper bound of the root; Newton from the right (convex decreasing f)
    for _ in range(60):
        x = c / (2 * Y)
        f = 2 * (NU * np.arctan(x)).sum(axis=0) - THETA
        fp = -(NU * c / (Y ** 2 + c ** 2 / 4)).sum(axis=0)
        Ynew = Y - f / fp
        if np.all(np.abs(Ynew - Y) <= 1e-13 * Y):
            Y = Ynew
            break
        Y = Ynew
    x = c / (2 * Y)
    Fc = c / 2 * np.log((1 + (1 / x) ** 2) / 4) + 2 * Y * np.arctan(x)
    Fc = np.where(NU > 0, Fc, 0.0)
    D0 = (NU * Fc).sum(axis=0) - THETA * Y - m
    G0 = m + S * math.log(2)
    D = D0 + g
    G = G0 - g
    return dict(m=m, Y=Y, D0=D0, G0=G0, gamma=g, D=D, G=G)


def E_batch(k, data, NU):
    NU = np.asarray(NU, dtype=np.float64)
    if NU.ndim == 1:
        NU = NU[:, None]
    g = gamma_batch(data, NU)
    r = rates_batch(data["L"], data["offsets"], NU, g)
    gap = r["D"] - (k - 1) * r["G"]
    E = np.where((r["G"] >= 0) & (gap > 0), r["m"] * (r["D"] + r["G"]) / np.where(gap > 0, gap, 1), np.inf)
    # require nu_0 >= 1
    E = np.where(NU[0] >= 1, E, np.inf)
    r["E"] = E
    r["gap"] = gap
    return r


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    d = build(69, tuple(range(12)), verbose=True)
    r = E_batch(3, d, np.array([66] + [11] * 11))
    print("E3 L69 twelve:", r["E"], "expect 1203.9724; gamma", r["gamma"])
    d = build(14, (0, 1), verbose=True)
    print("E3 two-layer:", E_batch(3, d, np.array([128, 128]))["E"], "expect 1762.608")
    d = build(99, tuple(range(29)), verbose=True)
    nu = np.array([64] + [4] * 27 + [0])
    r = E_batch(3, d, nu)
    print("E3 L99:", r["E"], "expect 1107.9268; gamma", r["gamma"], "expect 55.236264")
