"""N2 core: E_k for scaled shapes, asymptotic constants, integer refinement.

Float search tool only (cells exact via cells.build; gamma/rates in float64).
Any candidate must be re-certified with certify_any.py (Arb, code/certify.py).

Notation (shape v >= 0 on offsets t_j, c_j = 1-2t_j/L):
  V = sum v, S = sum v c, A = sum v c log c, gam = gamma(v) (homogeneous deg 1)
  g* = V + S log2 - gam,  d* = S log(S/Theta) - A - V + gam,  rho = exp(g*/S)
For nu = s v (s real): m = sV-1, G = s g* - 1, D = D0(s v) + s gam.
"""
import math
import sys
from pathlib import Path
import numpy as np
from scipy.optimize import minimize_scalar, brentq

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cells import build  # noqa: E402

THETA = math.pi / 2
_DATA = {}


def load(L, Tmax):
    key = (L, Tmax)
    if key not in _DATA:
        d = build(L, tuple(range(Tmax + 1)))
        d["Rf"] = d["R"].astype(np.float64)
        _DATA[key] = d
    return _DATA[key]


def gamma_batch(d, NU):
    NU = np.asarray(NU, dtype=np.float64)
    one = NU.ndim == 1
    if one:
        NU = NU[:, None]
    n = len(d["offsets"])
    if NU.shape[0] < n:
        NU = np.vstack([NU, np.zeros((n - NU.shape[0], NU.shape[1]))])
    V = d["Rf"] @ NU
    mins = np.minimum.reduceat(V, d["starts"], axis=0)
    g = d["ws"] @ mins
    return g[0] if one else g


def cvec(L, n):
    return np.array([1 - 2 * t / L for t in range(n)])


def shape_consts(L, v, gam):
    v = np.asarray(v, dtype=float)
    c = cvec(L, len(v))
    V, S = v.sum(), float(v @ c)
    A = float(np.sum(v * c * np.log(c)))
    gs = V + S * math.log(2) - gam
    ds = S * math.log(S / THETA) - A - V + gam
    rho = math.exp(gs / S)
    return dict(V=V, S=S, A=A, gam=gam, gs=gs, ds=ds, rho=rho)


def Yroot(nu, c):
    nu = np.asarray(nu, float)
    M = nu.sum()
    eq = lambda Y: 2 * np.sum(nu * np.arctan(c / (2 * Y))) - THETA
    return brentq(eq, 0.25, 4 * M + 10, xtol=1e-15 * max(1, M), rtol=1e-15, maxiter=500)


def rates_nu(L, nu, gam_nu):
    """Exact (float) rates for multiplicities nu (real allowed) with gamma(nu)=gam_nu."""
    nu = np.asarray(nu, float)
    c = cvec(L, len(nu))
    keep = nu > 0
    nu_, c_ = nu[keep], c[keep]
    M = nu_.sum(); m = M - 1
    Y = Yroot(nu_, c_)
    Fc = c_ / 2 * np.log((1 + (2 * Y / c_) ** 2) / 4) + 2 * Y * np.arctan(c_ / (2 * Y))
    D0 = float(np.sum(nu_ * Fc) - THETA * Y - m)
    G0 = float(m + np.sum(nu_ * c_) * math.log(2))
    D, G = D0 + gam_nu, G0 - gam_nu
    return dict(m=m, Y=Y, D0=D0, G0=G0, gamma=gam_nu, D=D, G=G)


def E_from_rates(k, r):
    gap = r["D"] - (k - 1) * r["G"]
    if r["G"] < 0 or gap <= 0:
        return math.inf
    return r["m"] * (r["D"] + r["G"]) / gap


def E_scaled(k, L, v, gam_v, s):
    v = np.asarray(v, float)
    return E_from_rates(k, rates_nu(L, s * v, s * gam_v))


def best_real_s(k, L, v, gam_v):
    """Minimise E_k(s v) over real s>0 (gamma exactly homogeneous)."""
    sc = shape_consts(L, v, gam_v)
    s0 = math.exp(((k - 1) * sc["gs"] - sc["ds"]) / sc["S"])
    f = lambda u: E_scaled(k, L, v, gam_v, s0 * math.exp(u))
    # coarse grid then bounded refine
    us = np.linspace(-0.5, 4.0, 46)
    vals = [f(u) for u in us]
    i = int(np.argmin(vals))
    lo, hi = us[max(i - 1, 0)], us[min(i + 1, len(us) - 1)]
    res = minimize_scalar(f, bounds=(lo, hi), method="bounded",
                          options=dict(xatol=1e-10))
    return dict(s=s0 * math.exp(res.x), u=res.x, E=res.fun, s0=s0, **sc)


def asym_E(k, sc):
    """Leading asymptotic: min_u of the large-s model.

    Model: D ~ s(S log s + d*) + 1, G = s g* - 1, m = sV - 1 dropped to sV.
    E ~ V s (D+G)/(D-(k-1)G); with s = s0 e^u:
      E ~ V s0 e^u (k g*/S + u)/u   minimised at u^2 + a u - a = 0, a=k g*/S.
    """
    a = k * sc["gs"] / sc["S"]
    u = (-a + math.sqrt(a * a + 4 * a)) / 2
    s0 = math.exp(((k - 1) * sc["gs"] - sc["ds"]) / sc["S"])
    return sc["V"] * s0 * math.exp(u) * (a + u) / u, u, s0


def int_refine(k, d, v, s, radius=None, extra=()):
    """Round s*v to integers, then local search over (nu_0, inner level) and
    per-coordinate +-1 moves; gamma recomputed exactly (float) each time."""
    L = d["L"]
    nu = np.maximum(np.rint(s * np.asarray(v, float)), 0)
    nz = np.nonzero(nu)[0]
    nu[nz] = np.maximum(nu[nz], 1)

    def Eval(nu_):
        g = gamma_batch(d, nu_)
        return E_from_rates(k, rates_nu(L, nu_, g))

    best = (Eval(nu), nu.copy())
    improved = True
    it = 0
    while improved and it < 60:
        improved = False
        it += 1
        cands = []
        for j in nz:
            for dlt in (-1, 1):
                x = best[1].copy(); x[j] += dlt
                if x[j] >= 1:
                    cands.append(x)
        # group moves: all inner coordinates with the same value +-1
        vals = sorted(set(best[1][nz[1:]].tolist()))
        for val in vals:
            idx = [j for j in nz[1:] if best[1][j] == val]
            for dlt in (-1, 1):
                x = best[1].copy(); x[idx] += dlt
                if x[idx].min() >= 1:
                    cands.append(x)
        # scale moves
        for fac in (0.995, 0.998, 1.002, 1.005):
            x = np.maximum(np.rint(best[1] * fac), 0); x[nz] = np.maximum(x[nz], 1)
            cands.append(x)
        NU = np.array(cands).T
        G = gamma_batch(d, NU)
        for col in range(NU.shape[1]):
            e = E_from_rates(k, rates_nu(L, NU[:, col], G[col]))
            if e < best[0] - 1e-12 * best[0]:
                best = (e, NU[:, col].copy()); improved = True
    return best


def two_level(T, w, lam=0.0):
    """v = (1, w x T, lam*w) on offsets 0..T(+1)."""
    v = [1.0] + [w] * T
    if lam > 0:
        v.append(lam * w)
    return np.array(v)


if __name__ == "__main__":
    d = load(69, 11)
    v = np.array([6.0] + [1.0] * 11)
    g = gamma_batch(d, v)
    sc = shape_consts(69, v, g)
    print("gamma* =", g, "(4.1305455731)", "g* =", sc["gs"], "(23.32693580313)",
          "rho =", sc["rho"])
    for k, s in [(3, 11), (5, 259), (7, 5871), (9, 131354)]:
        print(k, s, E_scaled(k, 69, v, g, s))
