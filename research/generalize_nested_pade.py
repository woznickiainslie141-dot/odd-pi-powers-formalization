"""Choose multiplicities in one fixed shape, then certify selected bounds."""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import minimize_scalar
from search_multilayer_pade import cells
from certify_nested_pade import certify

L=69
offsets=list(range(12))
models,W,psi=cells(L,tuple(offsets))
base=np.array([6]+[1]*11)
gamma_base=psi@np.einsum("cij,j->ci",W,base).min(axis=1)
c=1-2*np.arange(12)/L
rows=[]
for k in (3,5,7,9):
    def fun(lb):
        b=np.exp(lb)
        m=17*b-1
        nu=base*b
        Y=(nu@c)/(np.pi/2)
        for _ in range(5):
            Y-=(2*(nu@np.arctan(c/(2*Y)))-np.pi/2)/(-nu@(c/(Y*Y+c*c/4)))
        D0=nu@(c/2*np.log((1+(2*Y/c)**2)/4)
                   +2*Y*np.arctan(c/(2*Y)))-np.pi/2*Y-m
        G0=m+(nu@c)*np.log(2)
        gap=D0-(k-1)*G0+k*b*gamma_base
        return m*(D0+G0)/gap if gap>0 else 1e30
    opt=minimize_scalar(fun,bounds=(0,22),method="bounded")
    B=round(np.exp(opt.x))
    B=min(range(max(1,B-3),B+4),key=lambda b:fun(np.log(b)))
    value=fun(np.log(B))
    upper=str(int(np.floor(value))+1)
    row=certify(17*B-1,L,offsets,list(map(int,base*B)),upper,k=k)
    rows.append(row)
    print(json.dumps({s:row[s] for s in ("k","m","E","certified_strict_upper")}),
          flush=True)
data={"scope":"One shape only; no global optimization claim","rows":rows}
Path(__file__).with_name("nested_generalization_certificate_2026-10-27.json").write_text(
    json.dumps(data,indent=2)+"\n",encoding="utf-8")
