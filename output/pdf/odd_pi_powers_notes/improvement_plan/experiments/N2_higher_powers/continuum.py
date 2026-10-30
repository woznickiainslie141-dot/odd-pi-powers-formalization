"""Continuum limit of the arithmetic rate gamma (float, careful quadrature).

Shape: point mass v0 at theta=0 plus piecewise-constant density
omega_s on (a_s, b_s] (theta = t/L, c = 1-2 theta, 0 < a_s < b_s < 1/2).
Discrete shapes with nu_j = omega/L on t=1..T converge to it as L -> oo.

Exact identity (period-L argument, see report):
  gamma_L(mu) = int_0^oo f_mu(Z) Z^-2 dZ,
  f_mu(Z) = inf_y [ v0 [y>{Z}] + int W(theta;Z,y) dmu(theta) ],
  W = floor((1-2th)Z) - floor(y - th Z) - floor((1-th)Z - y).
For a step on (a,b] (B(x) = ({x}^2 - {x})/2):
  int_a^b W = (b-a)/2 + [F + B(y-bZ) - B(y-aZ) + B((1-a)Z-y) - B((1-b)Z-y)]/Z
  F = (b-a)/2*0 + int-part piece:  Fl = Ib - Ia,  Ix = int_0^x floor((1-2t)Z) dt
handled as Z*int_a^b floor((1-2t)Z)dt - Z(b-a)*((1-2a)Z+(1-2b)Z)/2*0 ... see code.
f is piecewise C^oo between the breakpoints n/alpha; the inf over y is over a
finite candidate set {0, {Z}, {aZ}, {(1-a)Z}, {bZ}, {(1-b)Z}}.
"""
import math
import numpy as np

THETA = math.pi / 2


def frac(x):
    return x - np.floor(x)


def Bf(x):
    u = frac(x)
    return 0.5 * (u * u - u)


def int_floor_lin(Z, a, b):
    """Z * int_a^b floor((1-2t) Z) dt, exactly (piecewise), vectorised in Z.

    With x=(1-2t)Z: = (1/2) int_{(1-2b)Z}^{(1-2a)Z} floor(x) dx.
    int_0^X floor = floor(X)*X - floor(X)(floor(X)+1)/2.
    Return value minus its smooth part (Z^2 (b-a)(1-a-b) - Z(b-a)/2) is bounded.
    """
    def G(X):
        n = np.floor(X)
        return n * X - n * (n + 1) / 2
    hi, lo = (1 - 2 * a) * Z, (1 - 2 * b) * Z
    return 0.5 * (G(hi) - G(lo))


def step_int_times_Z(Z, y, a, b):
    """Z * int_a^b W(theta; Z, y) dtheta.

    floor(y - tZ): Z int_a^b = int_{y-bZ}^{y-aZ} floor(x) dx
    floor((1-t)Z - y): Z int_a^b = int_{(1-b)Z-y}^{(1-a)Z-y} floor(x) dx
    int floor = x^2/2 - x/2 - B(x)  (antiderivative, continuous).
    """
    def Pf(x):  # antiderivative of floor, written to keep big parts explicit
        return 0.5 * x * x - 0.5 * x - Bf(x)
    t1 = int_floor_lin(Z, a, b)
    t2 = Pf(y - a * Z) - Pf(y - b * Z)
    t3 = Pf((1 - a) * Z - y) - Pf((1 - b) * Z - y)
    return t1 - t2 - t3


def step_int_times_Z_stable(Z, y, a, b):
    """Same as step_int_times_Z but with the polynomial parts cancelled
    analytically; returns Z*int W = Z(b-a)/2 + bounded."""
    # polynomial parts: t1_poly = 0.5*(G(hi)-G(lo)) with G(X)=X^2/2 - X/2 - B(X)
    # => Z*int_a^b W = (b-a)Z/2 + [ -B(hiZ)+B(loZ) ]/2 + B(y-aZ)-B(y-bZ)
    #                    + B((1-a)Z-y) - B((1-b)Z-y)   (algebra in report)
    hi, lo = (1 - 2 * a) * Z, (1 - 2 * b) * Z
    return ((b - a) * Z / 2 + 0.5 * (Bf(lo) - Bf(hi))
            + Bf(y - a * Z) - Bf(y - b * Z)
            + Bf((1 - a) * Z - y) - Bf((1 - b) * Z - y))


class Shape:
    def __init__(self, v0, steps):
        """steps: list of (a, b, omega) with 0 <= a < b < 1/2."""
        self.v0 = float(v0)
        self.steps = [(float(a), float(b), float(w)) for a, b, w in steps]
        bnds = sorted({x for a, b, _ in self.steps for x in (a, b)} - {0.0})
        self.betas = [1.0] + [x for x in bnds] + [1 - x for x in bnds]
        self.betas = sorted(set(self.betas))

    def V(self):
        return self.v0 + sum(w * (b - a) for a, b, w in self.steps)

    def S(self):
        # int (1-2t) = (b-a) - (b^2-a^2)
        return self.v0 + sum(w * ((b - a) - (b * b - a * a)) for a, b, w in self.steps)

    def A(self):
        # int_a^b c log c dt, c=1-2t, dt = -dc/2: = (1/2) int_{c(b)}^{c(a)} c log c dc
        def prim(c):
            return 0.5 * (c * c / 2 * math.log(c) - c * c / 4) if c > 0 else 0.0
        return sum(w * (prim(1 - 2 * a) - prim(1 - 2 * b)) for a, b, w in self.steps)

    def m_in(self):
        return sum(w * (b - a) for a, b, w in self.steps)

    def slopes(self):
        cands = [0.0, 1.0] + [x for a, b, _ in self.steps for x in (a, b, 1 - a, 1 - b)]
        bargs = [x for a, b, _ in self.steps for x in (a, b, 1 - a, 1 - b, 1 - 2 * a, 1 - 2 * b)] + [1.0]
        al = set()
        for c in cands:
            for x in bargs:
                for sgn in (1, -1):
                    d = abs(c - sgn * x)
                    if d > 1e-12:
                        al.add(round(d, 14))
        for c in cands:
            if c > 1e-12:
                al.add(round(c, 14))
        return sorted(al)

    def ZF(self, Z):
        """Z * f(Z) for an array Z (min over candidate y)."""
        Z = np.asarray(Z, float)
        fz = frac(Z)
        best = None
        cand_list = [np.zeros_like(Z), fz] + [frac(beta * Z) for beta in self.betas if beta != 1.0]
        for idx, y in enumerate(cand_list):
            val = np.zeros_like(Z)
            for a, b, w in self.steps:
                val += w * step_int_times_Z_stable(Z, y, a, b)
            if idx == 0:
                ind = 0.0           # y = 0+
            elif idx == 1:
                ind = 0.0           # y = {Z}-  (left limit; W_0 = 0)
            else:
                ind = (y > fz).astype(float)
            val += self.v0 * Z * ind
            best = val if best is None else np.minimum(best, val)
        return best


def breakpoints(shape, X):
    pts = [np.array([1.0, X])]
    for al in shape.slopes():
        n = np.arange(math.ceil(al * 1.0), math.floor(al * X) + 1)
        pts.append(n / al)
    p = np.unique(np.concatenate(pts))
    p = p[(p >= 1.0) & (p <= X)]
    # merge points closer than 1e-12 (coincident rational breakpoints)
    keep = np.concatenate([[True], np.diff(p) > 1e-11])
    return p[keep]


GL_X, GL_W = np.polynomial.legendre.leggauss(6)


def gamma_cont(shape, X=2e4, chunk=200000, split_crossings=True):
    """int_1^X f(Z)/Z^2 dZ + tail estimate.  f = 0 on (0,1)."""
    p = breakpoints(shape, X)
    total = 0.0
    tail_samples = []
    for i0 in range(0, len(p) - 1, chunk):
        lo = p[i0:i0 + chunk + 1][:-1]
        hi = p[i0:i0 + chunk + 1][1:]
        if split_crossings:
            # split each base interval at the crossings of candidate functions;
            # candidates are quadratic in Z on base intervals: locate kinks of
            # the min by sampling + quadratic fit is replaced by uniform split
            # into 4 sub-intervals plus 6-pt GL (kinks cost O(h^3) each).
            nsub = 4
            edges = lo[:, None] + (hi - lo)[:, None] * np.linspace(0, 1, nsub + 1)[None, :]
            a_, b_ = edges[:, :-1].ravel(), edges[:, 1:].ravel()
        else:
            a_, b_ = lo, hi
        mid, half = (a_ + b_) / 2, (b_ - a_) / 2
        Zn = mid[:, None] + half[:, None] * GL_X[None, :]
        ZF = shape.ZF(Zn.ravel()).reshape(Zn.shape)
        total += float(np.sum(half[:, None] * GL_W[None, :] * ZF / Zn ** 3))
        if hi[-1] > 0.9 * X:
            sel = Zn.ravel() > 0.9 * X
            tail_samples.append((Zn.ravel()[sel], ZF.ravel()[sel]))
    # tail: f = m_in/2 + H(Z)/Z ; int_X^oo f/Z^2 = m_in/(2X) + <H>/(2X^2) + ...
    Zs = np.concatenate([t[0] for t in tail_samples])
    ZFs = np.concatenate([t[1] for t in tail_samples])
    mi = shape.m_in()
    H = ZFs - mi / 2 * Zs
    tail = mi / (2 * X) + H.mean() / (2 * X * X)
    return total + tail, dict(n_intervals=len(p) - 1, tail=tail, Hmean=H.mean())


def rho_of(shape, gam):
    return 2 * math.exp((shape.V() - gam) / shape.S())


if __name__ == "__main__":
    import sys
    rng = np.random.default_rng(1)
    # check 1: stable formula vs direct numerical integration of W over theta
    for _ in range(5):
        Z, y = rng.uniform(1, 60), rng.uniform(0, 1)
        a, b = 0.05, 0.28
        th = np.linspace(a, b, 2000001)
        W = np.floor((1 - 2 * th) * Z) - np.floor(y - th * Z) - np.floor((1 - th) * Z - y)
        direct = Z * np.trapezoid(W, th)
        print("check stepint:", direct, step_int_times_Z_stable(Z, y, a, b), step_int_times_Z(Z, y, a, b))


# ---------------------------------------------------------------------------
# Exact-kink integrator: on each base interval every candidate Z*f_c(Z) is a
# quadratic polynomial in Z (B of a linear function without integer crossing),
# so fit it from 3 interior points, split at all pairwise crossings, and
# integrate min_c q_c(Z)/Z^3 with Gauss-Legendre on each smooth piece.

def ZF_cands(shape, Z):
    Z = np.asarray(Z, float)
    fz = frac(Z)
    out = []
    cand_list = [np.zeros_like(Z), fz] + [frac(beta * Z) for beta in shape.betas if beta != 1.0]
    for idx, y in enumerate(cand_list):
        val = np.zeros_like(Z)
        for a, b, w in shape.steps:
            val += w * step_int_times_Z_stable(Z, y, a, b)
        if idx >= 2:
            val += shape.v0 * Z * (y > fz)
        out.append(val)
    return np.array(out)


def gamma_exact_kinks(shape, X=2e4, chunk=100000, check=True):
    p = breakpoints(shape, X)
    total = 0.0
    maxres = 0.0
    us = np.array([0.2, 0.5, 0.8])
    tailZ, tailF = [], []
    for i0 in range(0, len(p) - 1, chunk):
        lo = p[i0:i0 + chunk + 1][:-1]
        hi = p[i0:i0 + chunk + 1][1:]
        h = hi - lo
        N = len(lo)
        Zs = lo[None, :] + h[None, :] * us[:, None]          # (3, N)
        F = ZF_cands(shape, Zs.ravel()).reshape(-1, 3, N)     # (C, 3, N)
        # quadratic in u through the 3 points: q(u) = c0 + c1 u + c2 u^2
        f0, f1, f2 = F[:, 0], F[:, 1], F[:, 2]
        # Lagrange at 0.2,0.5,0.8 (spacing 0.3)
        c2 = (f0 - 2 * f1 + f2) / (2 * 0.09)
        c1 = (f2 - f0) / 0.6 - c2 * 1.0          # derivative at 0.5 is (f2-f0)/0.6 = c1 + 2 c2*0.5
        c0 = f1 - c1 * 0.5 - c2 * 0.25
        if check:
            Zc = lo + h * 0.35
            Fc = ZF_cands(shape, Zc)
            qc = c0 + c1 * 0.35 + c2 * 0.35 ** 2
            maxres = max(maxres, float(np.max(np.abs(Fc - qc) / (1 + np.abs(Fc)))))
        C = F.shape[0]
        roots = []
        for i in range(C):
            for j in range(i + 1, C):
                A2, A1, A0 = c2[i] - c2[j], c1[i] - c1[j], c0[i] - c0[j]
                disc = A1 * A1 - 4 * A2 * A0
                with np.errstate(all="ignore"):
                    sq = np.sqrt(np.where(disc >= 0, disc, np.nan))
                    lin = np.abs(A2) < 1e-14 * (np.abs(A1) + np.abs(A0) + 1e-300)
                    r1 = np.where(lin, -A0 / A1, (-A1 + sq) / (2 * A2))
                    r2 = np.where(lin, np.nan, (-A1 - sq) / (2 * A2))
                roots += [r1, r2]
        R = np.array(roots).T                                   # (N, nr)
        R = np.where((R > 0) & (R < 1), R, np.nan)
        R = np.sort(R, axis=1)
        R = np.where(np.isnan(R), 1.0, R)
        E = np.concatenate([np.zeros((N, 1)), R, np.ones((N, 1))], axis=1)   # (N, nr+2)
        ua, ub = E[:, :-1], E[:, 1:]
        um, uh = (ua + ub) / 2, (ub - ua) / 2                   # (N, S)
        U = um[:, :, None] + uh[:, :, None] * GL_X[None, None, :]   # (N, S, 6)
        Q = (c0.T[:, None, None, :] + c1.T[:, None, None, :] * U[..., None]
             + c2.T[:, None, None, :] * U[..., None] ** 2)      # (N, S, 6, C)
        ZF = Q.min(axis=3)
        Z = lo[:, None, None] + h[:, None, None] * U
        w = (h[:, None] * uh)[:, :, None] * GL_W[None, None, :]
        total += float(np.sum(w * ZF / Z ** 3))
        sel = Z > 0.9 * X
        if sel.any():
            tailZ.append(Z[sel]); tailF.append(ZF[sel])
    Zt, Ft = np.concatenate(tailZ), np.concatenate(tailF)
    mi = shape.m_in()
    H = Ft - mi / 2 * Zt
    tail = mi / (2 * X) + H.mean() / (2 * X * X)
    return total + tail, dict(n_intervals=len(p) - 1, maxres=maxres, Hmean=float(H.mean()))
