"""Exact small examples; consistency checks, not asymptotic proofs."""
from fractions import Fraction as F
from math import factorial,comb,lcm,isqrt
from pathlib import Path
import json
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/"data"
DATA.mkdir(exist_ok=True)

def mul(a,b,d):
    return [sum((a[j]*b[k-j] for j in range(max(0,k-len(b)+1),
                min(k,len(a)-1)+1)),F(0)) for k in range(d+1)]

def coefficients(m,n,intervals):
    scale=factorial(m)*lcm(*range(1,n+1))**m
    out=[[[F(0) for _ in range(n+1)] for _ in range(m+1)]
         for _ in range(m+1)]
    for ell in range(n+1):
        multiplicity=sum(a<=ell<=b for a,b in intervals)
        if multiplicity==0:
            continue
        d=multiplicity-1
        series=[F(1)]+[F(0)]*d
        for a,b in intervals:
            constant=F(factorial(b-a))
            for r in range(a,b+1):
                if r==ell:
                    continue
                delta=r-ell
                constant/=delta
                series=mul(series,[F((-1)**j,delta**j)
                                   for j in range(d+1)],d)
            series=[constant*v for v in series]
        for h in range(m+1):
            poly=[F(comb(h,j)*(-ell)**(h-j)) for j in range(h+1)]
            product=mul(series,poly,d)
            for k in range(multiplicity):
                out[h][k][ell]=scale*product[multiplicity-1-k]/factorial(k)
    return out

def main():
    x=sp.Symbol("x")
    rows=[]
    for m,n,intervals in [
        (1,4,[(0,4),(1,3)]),
        (2,6,[(0,6),(0,6),(1,5)]),
        (3,8,[(0,8),(1,7),(1,7),(2,6)]),
    ]:
        A=coefficients(m,n,intervals)
        assert all(v.denominator==1 for row in A for col in row for v in col)
        matrix=sp.Matrix([[sum(int(v)*x**(n-j) for j,v in enumerate(col))
                           for col in row] for row in A])
        N=sum(b-a for a,b in intervals)
        offset=sum(n-b for a,b in intervals)
        determinant=sp.factor(matrix.det())
        constant=sp.cancel(determinant/(x**offset*(x-1)**N))
        assert constant.is_Rational and constant!=0
        for p in sp.primerange(isqrt(n)+1,n+1):
            for ell in range(n+1):
                w=sum((b-a)//p-(ell-a)//p-(b-ell)//p for a,b in intervals)
                for row in A:
                    for k,col in enumerate(row):
                        assert int(col[ell]) % p**(w+k)==0
        rows.append({"m":m,"n":n,"intervals":intervals,
                     "integer_coefficients":True,
                     "determinant_constant":str(constant),
                     "floor_divisibility_including_column_slack":True})
        if m==1:
            tex="\\[\n A_{1,4}(x)="+sp.latex(matrix)+" .\n\\]\n"
            (DATA/"toy_matrix.tex").write_text(tex,encoding="utf-8")
            print("Toy matrix:",matrix)
            print("Toy determinant:",determinant)
    data={"scope":"Finite exact consistency checks only","examples":rows}
    (DATA/"finite_checks.json").write_text(
        json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print("All exact checks passed.")

if __name__=="__main__":
    main()
