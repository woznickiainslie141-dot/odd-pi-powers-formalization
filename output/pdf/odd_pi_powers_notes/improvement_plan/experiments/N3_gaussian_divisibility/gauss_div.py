"""N3: exact A_{h,j,n}(x) in Z[x], evaluation at x=i, Gaussian valuations.

Definitions follow sections/02_algebra.tex exactly:
  Q_n(z)=prod_a prod_{r=alpha_a}^{beta_a}(z+r),  C_n=m! d_n^m prod_a ell_a!,
  z^h/Q_n = sum_l sum_r b_{h,l,r}/(z+l)^r,
  A_{h,j,n}(x)=(C_n/j!) sum_{l: mu_l>=j+1} b_{h,l,j+1} x^{n-l}.
Local Laurent data at the pole -l: z^h/Q = w^{-mu}(-l+w)^h B_l(w),
B_l(w)=B_l(0)*exp(sum_u (-1)^u sigma_u w^u/u), sigma_u=sum 1/(r-l)^u.
We work with D=d_n: s_u=D^u sigma_u and E_k=D^k [w^k](B_l/B_l(0)) are integers.

A[h][j][l] = integer coefficient of x^{n-l} in A_{h,j,n}(x).
All arithmetic is exact (Python ints / Fractions).
"""
from fractions import Fraction as Fr
from math import factorial, comb, gcd, isqrt, log
import sympy as sp

INF = 10 ** 9


def lcm_upto(n):
    r = 1
    for k in range(2, n + 1):
        r = r * k // gcd(r, k)
    return r


def groups_from(L, offsets, nu, n):
    assert n % L == 0
    N0 = n // L
    g = [(t * N0, n - t * N0, v) for t, v in zip(offsets, nu)]
    assert all(g[i][0] < g[i + 1][0] for i in range(len(g) - 1))
    return g


def expand(groups):
    out = []
    for a, b, v in groups:
        out += [(a, b)] * v
    return out


def coeff_matrix(n, groups):
    M = sum(v for _, _, v in groups)
    m = M - 1
    D = lcm_upto(n)
    base = factorial(m) * D ** m
    pw = [[0] * (n + 1) for _ in range(m + 1)]
    for u in range(1, m + 1):
        s = 0
        for e in range(1, n + 1):
            s += (D // e) ** u
            pw[u][e] = s
    Dpow = [D ** o for o in range(m + 1)]
    fact = [factorial(j) for j in range(m + 1)]
    A = [[[0] * (n + 1) for _ in range(M)] for _ in range(M)]
    for ell in range(n + 1):
        mu = sum(v for a, b, v in groups if a <= ell <= b)
        if mu == 0:
            continue
        d = mu - 1
        s = [0] * (d + 1)
        for a, b, v in groups:
            for u in range(1, d + 1):
                if a <= ell <= b:
                    val = pw[u][b - ell] + (-1) ** u * pw[u][ell - a]
                elif ell < a:
                    val = pw[u][b - ell] - pw[u][a - ell - 1]
                else:
                    val = (-1) ** u * (pw[u][ell - a] - pw[u][ell - b - 1])
                s[u] += v * val
        E = [1] + [0] * d
        for k in range(1, d + 1):
            acc = 0
            for u in range(1, k + 1):
                acc += (-1) ** u * s[u] * E[k - u]
            q, r = divmod(acc, k)
            assert r == 0
            E[k] = q
        Knum, Kden = base, 1
        for a, b, v in groups:
            la = b - a
            if a <= ell <= b:
                num, den = (-1) ** (ell - a) * comb(la, ell - a), 1
            elif ell < a:
                s_ = a - ell
                num, den = 1, s_ * comb(s_ + la, la)
            else:
                s_ = ell - b
                num, den = (-1) ** (la + 1), s_ * comb(s_ + la, la)
            Knum *= num ** v
            Kden *= den ** v
        g = gcd(Knum, Kden)
        Knum //= g
        Kden //= g
        for h in range(M):
            for j in range(mu):
                o = mu - 1 - j
                X = 0
                for i_ in range(min(h, o) + 1):
                    X += comb(h, i_) * (-ell) ** (h - i_) * E[o - i_] * Dpow[i_]
                q, r = divmod(Knum * X, Kden * fact[j] * Dpow[o])
                assert r == 0, ("non-integral", n, ell, h, j)
                A[h][j][ell] = q
    return A


# ---------------- Gaussian integer helpers (tuples (re, im)) -------------
def gmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def gsub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def gexactdiv(x, y):
    nrm = y[0] * y[0] + y[1] * y[1]
    a = x[0] * y[0] + x[1] * y[1]
    b = x[1] * y[0] - x[0] * y[1]
    qa, ra = divmod(a, nrm)
    qb, rb = divmod(b, nrm)
    assert ra == 0 and rb == 0
    return (qa, qb)


def ggcd(x, y):
    while y != (0, 0):
        nrm = y[0] * y[0] + y[1] * y[1]
        a = x[0] * y[0] + x[1] * y[1]
        b = x[1] * y[0] - x[0] * y[1]
        q = ((2 * a + nrm) // (2 * nrm), (2 * b + nrm) // (2 * nrm))
        x, y = y, gsub(x, gmul(q, y))
    return x


def gpow(x, e):
    r = (1, 0)
    while e:
        if e & 1:
            r = gmul(r, x)
        x = gmul(x, x)
        e >>= 1
    return r


def eval_at_i(poly, n):
    """poly[l] = coefficient of x^{n-l}; returns poly(i) as (re, im)."""
    re = im = 0
    for ell, c in enumerate(poly):
        if c:
            e = (n - ell) & 3
            if e == 0:
                re += c
            elif e == 1:
                im += c
            elif e == 2:
                re -= c
            else:
                im -= c
    return (re, im)


def bareiss_int(Mx):
    a = [row[:] for row in Mx]
    N = len(a)
    sign, prev = 1, 1
    for k in range(N - 1):
        if a[k][k] == 0:
            for r in range(k + 1, N):
                if a[r][k] != 0:
                    a[k], a[r] = a[r], a[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // prev
        prev = a[k][k]
    return sign * a[N - 1][N - 1]


def bareiss_gauss(Mx):
    a = [row[:] for row in Mx]
    N = len(a)
    sign, prev = 1, (1, 0)
    for k in range(N - 1):
        if a[k][k] == (0, 0):
            for r in range(k + 1, N):
                if a[r][k] != (0, 0):
                    a[k], a[r] = a[r], a[k]
                    sign = -sign
                    break
            else:
                return (0, 0)
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                a[i][j] = gexactdiv(gsub(gmul(a[i][j], a[k][k]),
                                         gmul(a[i][k], a[k][j])), prev)
        prev = a[k][k]
    d = a[N - 1][N - 1]
    return (sign * d[0], sign * d[1])


# ---------------- valuations ---------------------------------------------
def vp(a, p):
    if a == 0:
        return INF
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v


def sqrt_m1_mod(p, K):
    """rho with rho^2 = -1 mod p^K (p = 1 mod 4)."""
    r = int(sp.sqrt_mod(-1, p))
    mod = p
    while mod < p ** K:
        mod = min(mod * mod, p ** K)
        r = (r - (r * r + 1) * pow(2 * r, -1, mod)) % mod
    assert (r * r + 1) % (p ** K) == 0
    return r


def gauss_vals(z, p, rho=None, K=None):
    """Valuations of Gaussian integer z at the prime(s) above p.
    p=2 -> (v_{1+i},); p=3 mod 4 -> (v_p,); p=1 mod 4 -> (v_P, v_Pbar)
    with P=(p, i-rho)."""
    a, b = z
    if a == 0 and b == 0:
        return (INF,) if p % 4 != 1 else (INF, INF)
    if p == 2:
        va, vb = vp(a, 2), vp(b, 2)
        t = min(va, vb)
        a2, b2 = a >> t if a else 0, b >> t if b else 0
        extra = 1 if (a2 & 1) and (b2 & 1) else 0
        return (2 * t + extra,)
    if p % 4 == 3:
        return (min(vp(a, p), vp(b, p)),)
    pk = p ** K
    x1 = (a + b * rho) % pk
    x2 = (a - b * rho) % pk
    v1 = vp(x1, p) if x1 else K
    v2 = vp(x2, p) if x2 else K
    return (v1, v2)


def logprime(p, kind_index):
    """log |pi| for the Gaussian prime above p (norm^(1/2) convention)."""
    if p == 2 or p % 4 == 1:
        return 0.5 * log(p)
    return log(p)
