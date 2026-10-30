"""Sparse Type I Hermite-Pade experiment (T4 route 1).
Functions x^l * L^(k*j), L=log x, 0<=l<=n, 0<=j<=mp. Impose vanishing order
N=(mp+1)(n+1)-1 at x=1 (max possible), take the (generically 1-dim) integer kernel.
Evaluate at x=i: R = sum_j c_j pi^(k j), c_j in Z[i] after scaling by 2^(k mp).
Report kappa_n = log max|c_j| / n, delta_n = -log|R| / n (after removing integer content).
k=1 is the dense control (equals Mignotte's R_0 up to scalar).
Finite data only; no limit is proved.
"""
import sys, math, json, time
import flint, mpmath as mp
from math import comb, factorial
from functools import reduce

def stirling1_table(N):
    # signed Stirling numbers of the first kind s(s,e)
    S=[[0]*(N+1) for _ in range(N+1)]; S[0][0]=1
    for s in range(1,N+1):
        for e in range(1,s+1):
            S[s][e]=S[s-1][e-1]-(s-1)*S[s-1][e]
    return S

def run(k, mp_, n, S):
    cols=[(j,l) for j in range(mp_+1) for l in range(n+1)]
    N=(mp_+1)*(n+1)-1
    rows=[]
    for t in range(N):
        tf=factorial(t); row=[]
        for (j,l) in cols:
            e=k*j; ef=factorial(e); acc=0
            for s in range(e, t+1):
                if t-s<=l:
                    acc+=comb(l,t-s)*S[s][e]*(tf//factorial(s))
            row.append(acc*ef)
        rows.append(row)
    A=flint.fmpz_mat(rows)
    X,nul=A.nullspace()
    v=[int(X[i,0]) for i in range(len(cols))]
    g=reduce(math.gcd,v); v=[x//g for x in v]
    # c_j = 2^(k mp) * (i/2)^(k j) * sum_l v i^l  as Gaussian ints (re,im)
    ipow=[(1,0),(0,1),(-1,0),(0,-1)]
    cs=[]
    for j in range(mp_+1):
        re=im=0
        for l in range(n+1):
            a,b=ipow[l%4]; x=v[j*(n+1)+l]; re+=a*x; im+=b*x
        a,b=ipow[(k*j)%4]; sc=2**(k*(mp_-j))
        cs.append(((a*re-b*im)*sc,(a*im+b*re)*sc))
    cont=reduce(math.gcd,[abs(z) for c in cs for z in c])
    cs=[(a//cont,b//cont) for a,b in cs]
    H=max(math.hypot(a,b) if abs(a)<1e300 and abs(b)<1e300 else float(mp.sqrt(mp.mpf(a)**2+mp.mpf(b)**2)) for a,b in cs)
    dig=max(len(str(abs(z))) for c in cs for z in c)
    mp.mp.dps=2*dig+200
    P=mp.pi**k
    R=mp.mpc(0)
    for j,(a,b) in enumerate(cs):
        R+=mp.mpc(a,b)*P**j
    lR=float(mp.log(abs(R))) if R!=0 else float('-inf')
    lH=float(mp.log(mp.sqrt(mp.mpf(max(abs(z) for c in cs for z in c))**2*2)))
    return dict(k=k,mp=mp_,n=n,nullity=nul,kappa=lH/n,delta=-lR/n,digits=dig)

if __name__=="__main__":
    k=int(sys.argv[1]); mp_=int(sys.argv[2]); ns=[int(x) for x in sys.argv[3].split(',')]
    S=stirling1_table((mp_+1)*(max(ns)+1)+2)
    out=[]
    for n in ns:
        t0=time.time(); r=run(k,mp_,n,S); r['sec']=round(time.time()-t0,1)
        d,kp=r['delta'],r['kappa']
        r['E_proxy']= (mp_*(d+kp)/d if d>0 else None)
        print(json.dumps(r),flush=True); out.append(r)
