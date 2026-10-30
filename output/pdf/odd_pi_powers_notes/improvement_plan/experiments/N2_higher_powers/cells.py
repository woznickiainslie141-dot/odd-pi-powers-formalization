"""[N2 copy of N1_k3_search/cells.py, R stored as int8; gamma in float64.]
Fast exact arc partition (integer arithmetic) + batched float evaluator.

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
CACHE = Path(__file__).with_name("cache")
CACHE.mkdir(exist_ok=True)


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
    key = CACHE / f"L{L}_{'-'.join(map(str, offsets)) if len(offsets) < 12 else f'0to{offsets[-1]}_n{len(offsets)}_h{hash(offsets) & 0xffffffff:x}'}.pkl"
    if key.exists():
        with open(key, "rb") as f:
            return pickle.load(f)
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
    R = np.concatenate(mats).astype(np.int8)
    starts = np.cumsum([0] + [len(m) for m in mats[:-1]])
    data = dict(L=L, offsets=offsets, ws=ws, R=R, starts=starts,
                ncell=ncell, zero_cells=zero_cells, ngroups=len(mats),
                nrows=R.shape[0], secs=time.time() - t0)
    with open(key, "wb") as f:
        pickle.dump(data, f)
    if verbose:
        print(f"build L={L} n_off={len(offsets)}: cells={ncell} zero={zero_cells} "
              f"groups={len(mats)} rows={R.shape[0]} in {data['secs']:.1f}s", flush=True)
    return data


