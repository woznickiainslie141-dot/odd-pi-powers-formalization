"""N3 driver: coefficient content vs Pi_n, and Gaussian gcds of A(i).

usage: python analyze.py NAME L "t0,t1,.." "nu0,nu1,.." n_start n_stop n_step
Appends one JSON record per n to results/NAME.jsonl.
"""
import sys, json, time
from fractions import Fraction as Fr
from math import gcd, isqrt, log
from pathlib import Path
import sympy as sp
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from gauss_div import *
import fast_eval as fe


def f_pi(L, offsets, nu, N0, p):
    z = Fr(N0, p) % 1
    for a, b, rows in fe.arc_partition(L, tuple(offsets)):
        if z == a or z == b:
            return 0
        if a < z < b:
            return min(sum(r * v for r, v in zip(row, nu)) for row in rows)
    raise RuntimeError


def f_disc(groups, n, p):
    best = INF
    for ell in range(n + 1):
        s = sum(v * ((b - a) // p - (ell - a) // p - (b - ell) // p) for a, b, v in groups)
        best = min(best, s)
    return best


def rng(p, n):
    if p == 2:
        return "p2"
    if p * p <= n:
        return "small"
    if 2 * p <= n:
        return "mid"
    if p <= n:
        return "large"
    return "beyond"


def analyze(L, offsets, nu, n, euclid=True):
    t0 = time.time()
    groups = groups_from(L, offsets, nu, n)
    M = sum(nu); m = M - 1
    N = sum(v * (b - a) for a, b, v in groups)
    off = sum(v * (n - b) for a, b, v in groups)
    A = coeff_matrix(n, groups)
    t1 = time.time()
    # coefficient contents
    g_all = 0
    g_row = [0] * M
    g_col = [0] * M
    for h in range(M):
        for j in range(M):
            for c in A[h][j]:
                if c:
                    g_row[h] = gcd(g_row[h], c)
                    g_col[j] = gcd(g_col[j], c)
    for h in range(M):
        g_all = gcd(g_all, g_row[h])
    Ai = [[eval_at_i(A[h][j], n) for j in range(M)] for h in range(M)]
    alphas = [a for a, b, v in groups for _ in range(v)]
    lead = [[A[h][j][alphas[j]] for j in range(M)] for h in range(M)]
    cn = abs(bareiss_int(lead))
    assert cn != 0
    # factor c_n over primes <= max(n, m)
    primes = list(sp.primerange(2, max(n, m) + 1))
    cfac = {}
    rest = cn
    for p in primes:
        v = 0
        while rest % p == 0:
            rest //= p; v += 1
        if v:
            cfac[p] = v
    assert rest == 1, "c_n has a prime factor > max(n,m)"
    # determinant check at x=i
    detok = None
    if M <= 6:
        di = bareiss_gauss(Ai)
        pred = gmul(gpow((0, 1), off), gpow((-1, 1), N))
        detok = (di == gmul((cn, 0), pred)) or (di == gmul((-cn, 0), pred))
    keys = ["p2", "small", "mid", "large", "beyond"]
    Lcoef = {k: 0.0 for k in keys}
    LPi = 0.0; Lfdisc = 0.0
    Lmat = {k: 0.0 for k in keys}
    Lrow = [{k: 0.0 for k in keys} for _ in range(M)]
    Lcol = [{k: 0.0 for k in keys} for _ in range(M)]
    Lcoefrow = [{k: 0.0 for k in keys} for _ in range(M)]
    split_inert = {"split": [0.0, 0.0], "inert": [0.0, 0.0], "ram": [0.0, 0.0]}  # [extra_mat, extra_row0..]
    extra_primes = []
    pred_cmp = []  # (p, fPi, fdisc, vcoef) for sqrt n < p <= n
    two_adic = {}
    for p in primes:
        vcoef = vp(g_all, p)
        r = rng(p, n)
        lp = log(p)
        Lcoef[r] += vcoef * lp
        if p * p > n and p <= n:
            fp = f_pi(L, offsets, nu, n // L, p)
            fd = f_disc(groups, n, p)
            LPi += fp * lp; Lfdisc += fd * lp
            pred_cmp.append((p, fp, fd, vcoef))
            assert fp <= fd <= vcoef, ("lemma violated", p, fp, fd, vcoef)
        for h in range(M):
            Lcoefrow[h][r] += vp(g_row[h], p) * lp
        vc = cfac.get(p, 0)
        if p == 2:
            Vdet = (2 * vc + N,)
        elif p % 4 == 1:
            Vdet = (vc, vc)
        else:
            Vdet = (vc,)
        if max(Vdet) == 0:
            continue
        rho = sqrt_m1_mod(p, vc + 2) if p % 4 == 1 else None
        vals = [[gauss_vals(Ai[h][j], p, rho, vc + 2) for j in range(M)] for h in range(M)]
        ncomp = len(Vdet)
        lw = logprime(p, 0)
        vcg = 2 * vcoef if p == 2 else vcoef  # coefficient content at each Gaussian prime above p
        kind = "ram" if p == 2 else ("split" if p % 4 == 1 else "inert")
        for c in range(ncomp):
            vm = min(vals[h][j][c] for h in range(M) for j in range(M))
            vr = [min(vals[h][j][c] for j in range(M)) for h in range(M)]
            vcl = [min(vals[h][j][c] for h in range(M)) for j in range(M)]
            assert vm <= Vdet[c] and all(x <= Vdet[c] for x in vr)
            assert vm >= vcg
            Lmat[r] += vm * lw
            for h in range(M):
                Lrow[h][r] += vr[h] * lw
                Lcol[h][r] += vcl[h] * lw
            if vm > vcg or max(vr) > vcg:
                extra_primes.append(dict(p=p, comp=c, kind=kind, vcoef=vcg, vmat=vm,
                                         vrow=vr, vcol=vcl, vdet=Vdet[c]))
            split_inert[kind][0] += (vm - vcg) * lw
            split_inert[kind][1] += (min(vr) - vcg) * lw
            if p == 2:
                two_adic = dict(N=N, vdet=Vdet[0], vcoef_1pi=vcg,
                                col0=[vals[h][0][0] for h in range(M)],
                                rows=vr, cols=vcl,
                                entries=[[vals[h][j][0] for j in range(M)] for h in range(M)])
    S = lambda d: sum(d.values())
    rec = dict(L=L, offsets=list(offsets), nu=list(nu), n=n, M=M, N=N,
               log_cn=log(cn), cn_bits=cn.bit_length(),
               logPi=LPi, logfdisc=Lfdisc, logcoef=S(Lcoef), logcoef_by=Lcoef,
               logmat=S(Lmat), logmat_by=Lmat,
               logrow=[S(x) for x in Lrow], logrow_by=Lrow,
               logcol=[S(x) for x in Lcol],
               logcoefrow=[S(x) for x in Lcoefrow],
               logdet=log(cn) + 0.5 * N * log(2),
               max_entry_log=max(0.5 * log(max(1, a * a + b * b)) for row in Ai for a, b in row),
               extra_by_kind=split_inert,
               extra_primes=extra_primes, pred_cmp=pred_cmp, two_adic=two_adic,
               det_check=detok, t_coef=t1 - t0)
    if euclid:
        g = (0, 0)
        for row in Ai:
            for e in row:
                g = ggcd(e, g) if g != (0, 0) else e
        rec["euclid_logmat"] = 0.5 * log(g[0] ** 2 + g[1] ** 2)
        rr = []
        for row in Ai:
            g = row[0]
            for e in row[1:]:
                g = ggcd(e, g)
            rr.append(0.5 * log(g[0] ** 2 + g[1] ** 2))
        rec["euclid_logrow"] = rr
    # alternative integral unimodular row basis (z + n/2)^h : same matrix gcd, rows may differ
    from math import comb as _comb
    c0 = n // 2
    Bi = []
    for h in range(M):
        row = []
        for j in range(M):
            re = sum(_comb(h, k) * c0 ** (h - k) * Ai[k][j][0] for k in range(h + 1))
            im = sum(_comb(h, k) * c0 ** (h - k) * Ai[k][j][1] for k in range(h + 1))
            row.append((re, im))
        Bi.append(row)
    lrB = []
    for row in Bi:
        g = row[0]
        for e in row[1:]:
            g = ggcd(e, g)
        lrB.append(0.5 * log(g[0] ** 2 + g[1] ** 2))
    rec["euclid_logrow_shift"] = lrB
    rec["t_total"] = time.time() - t0
    return rec


def main():
    name, L = sys.argv[1], int(sys.argv[2])
    offsets = tuple(int(s) for s in sys.argv[3].split(","))
    nu = tuple(int(s) for s in sys.argv[4].split(","))
    n0, n1, st = int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    out = HERE / "results"
    out.mkdir(exist_ok=True)
    gam = fe.gamma(L, offsets, nu) if L >= 2 else 0.0
    with open(out / f"{name}.jsonl", "a") as fh:
        for n in range(n0, n1 + 1, st):
            rec = analyze(L, offsets, nu, n)
            rec["gamma_formula"] = gam
            fh.write(json.dumps(rec) + "\n"); fh.flush()
            mr = min(rec["logrow"])
            print(f"n={n:4d} M={rec['M']} logPi/n={rec['logPi']/n:.4f} coef/n={rec['logcoef']/n:.4f} "
                  f"mat/n={rec['logmat']/n:.4f} minrow/n={mr/n:.4f} "
                  f"(mat-coef)/n={(rec['logmat']-rec['logcoef'])/n:.4f} (minrow-coef)/n={(mr-rec['logcoef'])/n:.4f} "
                  f"det={rec['det_check']} eu={rec.get('euclid_logmat',0)-rec['logmat']:.2e} t={rec['t_total']:.1f}s",
                  flush=True)


if __name__ == "__main__":
    main()
