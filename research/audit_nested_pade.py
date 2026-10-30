"""Exact finite audits and a bounded numerical search, not an optimality proof."""
from fractions import Fraction as F
from math import factorial, comb, lcm, log, isqrt
from pathlib import Path
import json
import numpy as np
from scipy.special import digamma

OUT = Path(__file__).resolve().parent


def mul(a, b, d):
    return [sum((a[j] * b[k-j] for j in range(max(0,k-len(b)+1),
                   min(k,len(a)-1)+1)), F(0)) for k in range(d+1)]


def coefficients(m, n, intervals):
    """Columns are coefficient lists indexed by lambda, before evaluating x=i."""
    den = lcm(*range(1,n+1)) ** m * factorial(m)
    ans = [[[F(0) for _ in range(n+1)] for _ in range(m+1)]
           for _ in range(m+1)]
    for ell in range(n+1):
        mult = sum(a <= ell <= b for a,b in intervals)
        if not mult:
            continue
        d = mult-1
        s = [F(1)] + [F(0)]*d
        for a,b in intervals:
            constant = F(factorial(b-a))
            for r in range(a,b+1):
                if r == ell:
                    continue
                delta = r-ell
                constant /= delta
                s = mul(s, [F((-1)**j,delta**j) for j in range(d+1)], d)
            s = [constant*v for v in s]
        for h in range(m+1):
            poly = [F(comb(h,j)*(-ell)**(h-j)) for j in range(h+1)]
            prod = mul(s, poly, d)
            for k in range(mult):
                ans[h][k][ell] = den*prod[mult-1-k]/factorial(k)
    return ans


def evaluate_i(column, n):
    real = sum((v*((-1)**((n-j)//2)) for j,v in enumerate(column)
                if (n-j)%2 == 0), F(0))
    imag = sum((v*((-1)**((n-j-1)//2)) for j,v in enumerate(column)
                if (n-j)%2), F(0))
    assert real.denominator == imag.denominator == 1
    return int(real),int(imag)


def gcd_g(a,b):
    while b != (0,0):
        norm=b[0]**2+b[1]**2
        qr=(2*(a[0]*b[0]+a[1]*b[1])+norm)//(2*norm)
        qi=(2*(a[1]*b[0]-a[0]*b[1])+norm)//(2*norm)
        a,b=b,(a[0]-qr*b[0]+qi*b[1],a[1]-qr*b[1]-qi*b[0])
    return a


def exact_audit():
    import sympy as sp
    x=sp.Symbol("x")
    tests=[]
    for m,n,intervals in [
        (1,4,[(0,4),(1,3)]),
        (2,6,[(0,6),(0,6),(1,5)]),
        (3,8,[(0,8),(1,7),(1,7),(2,6)]),
    ]:
        A=coefficients(m,n,intervals)
        assert all(v.denominator == 1 for row in A for col in row for v in col)
        mat=sp.Matrix([[sum(int(v)*x**(n-j) for j,v in enumerate(col))
                        for col in row] for row in A])
        N=sum(b-a for a,b in intervals)
        offset=sum(n-b for a,b in intervals)
        quotient=sp.cancel(mat.det()/(x**offset*(x-1)**N))
        assert quotient.is_Rational and quotient != 0
        # Proposed floor-function lower bound on every polynomial coefficient.
        for p in list(sp.primerange(isqrt(n)+1,n+1)):
            for ell in range(n+1):
                w=sum((b-a)//p-(ell-a)//p-(b-ell)//p
                      for a,b in intervals)
                for row in A:
                    for col in row:
                        assert int(col[ell]) % (p**w) == 0
        tests.append({"m":m,"n":n,"intervals":intervals,
                      "integer_coefficients":True,"determinant_verified":True,
                      "determinant_constant":str(quotient),
                      "floor_divisibility_verified":True})
    gcd_rows=[]
    for m in (2,3,4):
        for n in (4,10,20,40):
            A=coefficients(m,n,[(0,n)]*(m+1))
            for h,row in enumerate(A):
                g=(0,0)
                for col in row:
                    g=gcd_g(g,evaluate_i(col,n))
                norm=g[0]**2+g[1]**2
                gcd_rows.append({"m":m,"n":n,"h":h,"gcd":g,
                                 "log_abs_g_over_n":log(norm)/(2*n)})
    return {"finite_checks_only":True,"nested_examples":tests,
            "original_gcd_rows":gcd_rows}


def search_two_layers(max_m=700,max_L=150):
    ms,rs=np.tril_indices(max_m+1,-1)
    keep=(ms>=2)&(rs>=1)
    m=ms[keep].astype(float)
    r=rs[keep].astype(float)
    M=m+1
    best=[]
    smallest_feasible=None
    for L in range(3,max_L+1):
        c=(L-2)/L
        k=np.arange(1,L-1,dtype=float)
        gl=sum(digamma(k/(L-1))-digamma(np.maximum(k/L,(k-1)/(L-2))))/L
        gamma=np.minimum(r,M-r)*gl
        S=r+(M-r)*c
        Y=S/(np.pi/2)
        for _ in range(5):
            f=2*r*np.arctan(1/(2*Y))+2*(M-r)*np.arctan(c/(2*Y))-np.pi/2
            fp=-r/(Y*Y+.25)-(M-r)*c/(Y*Y+c*c/4)
            Y-=f/fp
        def term(cc):
            return cc/2*np.log((1+(2*Y/cc)**2)/4)+2*Y*np.arctan(cc/(2*Y))
        D0=r*term(1)+(M-r)*term(c)-np.pi/2*Y-m
        G0=m+S*np.log(2)
        gap=D0-2*G0+3*gamma
        values=np.where(gap>0,m*(D0+G0)/gap,np.inf)
        ix=np.argmin(values)
        best.append({"m":int(m[ix]),"L":L,"r":int(r[ix]),
                     "D0":float(D0[ix]),"G0":float(G0[ix]),
                     "gamma":float(gamma[ix]),"E":float(values[ix])})
        feasible=m[gap>0]
        if len(feasible):
            v=int(np.min(feasible))
            smallest_feasible=v if smallest_feasible is None else min(v,smallest_feasible)
    best.sort(key=lambda d:d["E"])
    return {"scope":{"m_min":2,"m_max":max_m,"L_min":3,"L_max":max_L,
                     "r":"1,...,m"},"floating_search_only":True,
            "smallest_m_with_positive_gap":smallest_feasible,"best":best[:15]}


if __name__=="__main__":
    data={"exact":exact_audit(),"two_layer_search":search_two_layers()}
    (OUT/"nested_pade_audit_2026-10-27.json").write_text(
        json.dumps(data,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"nested_checks":data["exact"]["nested_examples"],
        "search":data["two_layer_search"],
        "gcd_h0":[r for r in data["exact"]["original_gcd_rows"] if r["h"]==0]},
        ensure_ascii=False,indent=2))
