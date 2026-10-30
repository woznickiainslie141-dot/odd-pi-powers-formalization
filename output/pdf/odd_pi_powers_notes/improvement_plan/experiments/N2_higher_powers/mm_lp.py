"""Shape optimisation by LP on reduced (minimal-row, merged) cells.

mode rho : minimise V - gamma  s.t. S = 1           (exact LP for rho)
mode k   : majorise-minimise the large-s model of log E_k (see hp.asym_E):
   Phi(v) = log V + (k-1) g* - d* + log h(k g*/S)   (scale invariant, S=1)
   concave parts (log V, log h) linearised at the current v ->
   minimise  V(1 + 1/(V0 k (1+kap))) - gamma + A/(k(1+kap)),  kap=1/(a0+u0).
usage: python mm_lp.py L Tmax rho|k [iters]
"""
import sys
import math
import time
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from hp import load, gamma_batch, shape_consts, asym_E, best_real_s, int_refine, cvec, THETA


def lp(d, cV, cA, v0_min=1e-7):
    L = d["L"]
    n = len(d["offsets"])
    R = d["R"]
    starts = d["starts"]
    ng = len(starts)
    nr = R.shape[0]
    grp = np.zeros(nr, dtype=np.int64)
    grp[starts[1:]] = 1
    grp = np.cumsum(grp)
    rr, cc = np.nonzero(R)
    rows = np.concatenate([rr, np.arange(nr)])
    cols = np.concatenate([cc, n + grp])
    vals = np.concatenate([-np.ones(len(rr)), np.ones(nr)])
    A = coo_matrix((vals, (rows, cols)), shape=(nr, n + ng)).tocsr()
    c = cvec(L, n)
    clogc = c * np.log(c)
    cost = np.concatenate([cV * np.ones(n) + cA * clogc, -d["ws"]])
    Aeq = np.concatenate([c, np.zeros(ng)])[None, :]
    bounds = [(v0_min, None)] + [(0, None)] * (n - 1) + [(None, None)] * ng
    res = linprog(cost, A_ub=A, b_ub=np.zeros(nr), A_eq=Aeq, b_eq=[1.0],
                  bounds=bounds, method="highs")
    assert res.status == 0, res.message
    return res.x[:n]


def describe(v, tol=1e-7):
    v = v / v[0]
    return ", ".join(f"{t}:{x:.5f}" for t, x in enumerate(v) if x > tol)


if __name__ == "__main__":
    L, Tmax = int(sys.argv[1]), int(sys.argv[2])
    mode = sys.argv[3]
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    t0 = time.time()
    d = load(L, Tmax)
    print(f"L={L} Tmax={Tmax} groups={len(d['starts'])} rows={d['nrows']} ({time.time()-t0:.1f}s)", flush=True)
    out = {}
    if mode == "rho":
        v = lp(d, 1.0, 0.0)
        g = gamma_batch(d, v)
        sc = shape_consts(L, v, g)
        print(f"rho_LP={sc['rho']:.8f} ({time.time()-t0:.1f}s)\n  shape: {describe(v)}", flush=True)
        out = dict(L=L, Tmax=Tmax, rho=sc["rho"], v=(v / v[0]).tolist())
    else:
        k = int(mode)
        v = lp(d, 1.0, 0.0)  # start from rho-optimal shape
        hist = []
        for it in range(iters):
            g = gamma_batch(d, v)
            sc = shape_consts(L, v, g)
            Ea, u0, s0 = asym_E(k, sc)
            a0 = k * sc["gs"] / sc["S"]
            kap = 1 / (a0 + u0)
            V0 = sc["V"] / sc["S"]
            r = best_real_s(k, L, v, g)
            hist.append((Ea, r["E"]))
            print(f" it={it} asymE={Ea:.6f} exactE(real s)={r['E']:.6f} rho={sc['rho']:.6f} "
                  f"({time.time()-t0:.1f}s)", flush=True)
            cV = 1 + 1 / (V0 * k * (1 + kap))
            cA = 1 / (k * (1 + kap))
            v = lp(d, cV, cA)
        g = gamma_batch(d, v)
        r = best_real_s(k, L, v, g)
        print(f" final exactE(real s)={r['E']:.6f} s={r['s']:.3f}\n  shape: {describe(v)}", flush=True)
        Eint, nu = int_refine(k, d, v, r["s"])
        nu = nu.astype(int).tolist()
        while nu and nu[-1] == 0:
            nu.pop()
        print(f" integer E={Eint:.6f} nu={nu}", flush=True)
        out = dict(L=L, Tmax=Tmax, k=k, E_real=r["E"], E_int=Eint, nu=nu,
                   v=(v / v[0]).tolist())
    with open(f"mmlp_L{L}_{mode}.json", "w") as f:
        json.dump(out, f, indent=1)
