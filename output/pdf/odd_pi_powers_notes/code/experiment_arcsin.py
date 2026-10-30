"""Finite experiment: scalar diagonal Pade for (arcsin(sqrt z)/sqrt z)^3."""
from pathlib import Path
from math import comb
from flint import fmpq, fmpq_mat
import mpmath as mp
import json

max_n=32
mp.mp.dps=5000
f=[fmpq(comb(2*j,j),4**j*(2*j+1)) for j in range(2*max_n+1)]
f2=[sum((f[j]*f[k-j] for j in range(k+1)),fmpq(0)) for k in range(len(f))]
c=[sum((f[j]*f2[k-j] for j in range(k+1)),fmpq(0)) for k in range(len(f))]
rows=[]
for n in (2,4,6,8,10,12,16,20,24,28,32):
    mat=fmpq_mat([[c[n+i-j] for j in range(1,n+1)] for i in range(1,n+1)])
    rhs=fmpq_mat([[-c[n+i]] for i in range(1,n+1)])
    sol=mat.solve(rhs)
    q=[fmpq(1)]+[sol[j,0] for j in range(n)]
    p=[sum((q[j]*c[k-j] for j in range(k+1)),fmpq(0)) for k in range(n+1)]
    z=fmpq(1,4)
    pv=sum((p[j]*z**j for j in range(n+1)),fmpq(0))
    qv=sum((q[j]*z**j for j in range(n+1)),fmpq(0))
    value=27*pv/qv
    P,Q=int(value.p),int(value.q)
    err=abs(mp.pi**3-mp.mpf(P)/Q)
    logQ=mp.log(Q)
    L=err*Q
    rows.append({"n":n,"log_Q_over_n":float(logQ/n),
                 "minus_log_linear_form_over_n":float(-mp.log(L)/n),
                 "approximation_error_exponent":float(-mp.log(err)/logQ),
                 "denominator_digits":len(str(Q))})
out=(Path(__file__).resolve().parents[1]/"data"/"experiment_arcsin.json")
out.write_text(json.dumps({"finite_data_only":True,"rows":rows},indent=2)+"\n",
               encoding="utf-8")
print(json.dumps(rows,indent=2))
