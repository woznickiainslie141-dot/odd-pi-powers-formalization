"""Exact screening of a pure beta(3) family from second derivatives.

R_n(t) has simple poles at -k-1/2 and triple zeros at 0,...,n-1.
Summing (-1)^t R_n''(t)/2 therefore introduces beta(3) only.
The script screens primitive integer linear forms; finite data prove no limit.
"""
from math import factorial,comb,gcd
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
import json

mp.mp.dps=2500
rows=[]
for a in range(3,9):
    for n in (2,4,8,12,20,30,40):
        tail=F(0)
        q=0
        p=F(0)
        for k in range(a*n+1):
            b=F(factorial(2*k+2*n)*factorial(k),
                factorial(2*k)*factorial(k+n)*factorial(n))
            assert b.denominator == 1
            ck=comb(a*n,k)*int(b)**3
            # Overall sign (-1)^n of R is immaterial.
            q+=8*ck
            p+=ck*tail
            tail+=F(8*((-1)**k),(2*k+1)**3)
        D=p.denominator
        Q=q*D
        P=p.numerator
        g=gcd(Q,P)
        Q//=g
        P//=g
        # P/Q approximates beta(3).
        err=abs(mp.pi**3/32-mp.mpf(P)/Q)
        delta=-mp.log(err*Q)/n
        kappa=mp.log(Q)/n
        rows.append({"a":a,"n":n,"kappa_n":float(kappa),
                     "delta_n":float(delta),
                     "error_exponent":float(-mp.log(err)/mp.log(Q)),
                     "primitive_denominator_digits":len(str(Q))})
data={"finite_data_only":True,"rows":rows}
Path(__file__).with_name("derivative_beta3_screen_2026-10-27.json").write_text(
    json.dumps(data,indent=2)+"\n",encoding="utf-8")
print(json.dumps([r for r in rows if r["n"] in (8,20,40)],indent=2))
