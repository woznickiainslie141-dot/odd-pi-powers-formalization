"""Continuous relaxation: minimise E_k over real nu >= 0 (nu_0 >= 1) at fixed L.

Analytic (sub)gradient: dgamma/dnu = sum_g w_g * argmin-row_g;
dD0/dnu_j = F_{c_j}(Y) - 1 (envelope: dF_c/dY = 2 arctan(c/2Y), saddle eq.);
dG0/dnu_j = 1 + c_j log 2.  Float only; heuristic lower envelope for the
integer problem (gamma is concave piecewise linear, L-BFGS-B may stall at kinks).
usage: python cont_opt.py k L [L ...]
"""
import sys
import json
import math
import numpy as np
from scipy.optimize import minimize
from common import build, tmax_for
from cells import rates_batch

THETA = math.pi / 2


def make_fun(k, data):
    R = data["R"].astype(np.float64)
    starts = data["starts"]
    ws = data["ws"]
    L, offs = data["L"], data["offsets"]
    c = np.array([1 - 2 * t / L for t in offs])
    ends = np.append(starts[1:], R.shape[0])

    def fun(nu):
        V = R @ nu
        # argmin row per group
        g = 0.0
        dg = np.zeros_like(nu)
        mins = np.minimum.reduceat(V, starts)
        g = ws @ mins
        # rows achieving min: take first per group
        is_min = V == np.repeat(mins, ends - starts)
        grp = np.repeat(np.arange(len(starts)), ends - starts)
        idx = np.nonzero(is_min)[0]
        first = idx[np.unique(grp[idx], return_index=True)[1]]
        dg = (ws[:, None] * R[first]).sum(axis=0)
        r = rates_batch(L, offs, nu[:, None], np.array([g]))
        Y = r["Y"][0]
        m = r["m"][0]
        D, G = r["D"][0], r["G"][0]
        x = c / (2 * Y)
        Fc = c / 2 * np.log((1 + (1 / x) ** 2) / 4) + 2 * Y * np.arctan(x)
        dD = Fc - 1 + dg
        dG = 1 + c * math.log(2) - dg
        gap = D - (k - 1) * G
        if gap <= 0 or G < 0:
            return 1e9, np.zeros_like(nu)
        N = D + G
        E = m * N / gap
        dE = N / gap + m * (dD + dG) / gap - m * N / gap ** 2 * (dD - (k - 1) * dG)
        return E, dE
    return fun


def run(k, L, nu0=None):
    Tmax = tmax_for(L)
    offs = tuple(range(Tmax + 1))
    data = build(L, offs)
    n = len(offs)
    if nu0 is None:
        nu0 = np.zeros(n)
        nu0[0] = 64
        nu0[1:int(0.34 * L) + 1] = 330 / L
    fun = make_fun(k, data)
    bounds = [(1, None)] + [(0, None)] * (n - 1)
    best = None
    x = np.asarray(nu0, dtype=float)
    for rep in range(6):
        res = minimize(fun, x, jac=True, method="L-BFGS-B", bounds=bounds,
                       options=dict(maxiter=3000, maxfun=6000, ftol=1e-13, gtol=1e-9))
        if best is None or res.fun < best.fun - 1e-9:
            best = res
            x = res.x + np.random.default_rng(rep).normal(0, 0.05, n) * (res.x > 0.01)
            x = np.maximum(x, 0); x[0] = max(x[0], 1)
        else:
            break
    nu = best.x
    r = rates_batch(L, offs, nu[:, None], np.array([fun(nu)[0] * 0]))  # placeholder
    return dict(k=k, L=L, E=float(best.fun), nu=[round(float(v), 3) for v in nu],
                M=float(nu.sum()), m=float(nu.sum() - 1))


if __name__ == "__main__":
    k = int(sys.argv[1])
    for L in map(int, sys.argv[2:]):
        res = run(k, L)
        with open(f"cont_k{k}.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(res) + "\n")
        nz = [v for v in res["nu"] if v > 1e-3]
        print(f"L={L}: Econt={res['E']:.4f} m={res['m']:.2f} nu0={res['nu'][0]:.2f} "
              f"support={len(nz)} inner={[round(v,2) for v in res['nu'][1:len(nz)+3]]}", flush=True)
