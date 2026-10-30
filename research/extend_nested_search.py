"""A few more finite searches; no assertion of global optimality."""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import differential_evolution
from search_multilayer_pade import cells,evaluate

results=[]
for J,L in [(8,45),(10,57),(12,69)]:
    models,W,psi=cells(L,tuple(range(J)))
    c=1-2*np.arange(J)/L
    def obj(raw):
        m,p0=raw
        M=m+1
        proportions=np.array([p0]+[(1-p0)/(J-1)]*(J-1))
        gamma_per_M=psi@np.einsum("cij,j->ci",W,proportions).min(axis=1)
        weights=M*proportions
        Y=(weights@c)/(np.pi/2)
        for _ in range(4):
            Y-=(2*(weights@np.arctan(c/(2*Y)))-np.pi/2)/(-weights@(c/(Y*Y+c*c/4)))
        D0=weights@(c/2*np.log((1+(2*Y/c)**2)/4)+2*Y*np.arctan(c/(2*Y)))-np.pi/2*Y-m
        G0=m+(weights@c)*np.log(2)
        gap=D0-2*G0+3*M*gamma_per_M
        return m*(D0+G0)/gap if gap>0 else 1e8
    opt=differential_evolution(obj,[(100,350),(.15,.8)],seed=20261027,popsize=7,
                               maxiter=60,tol=1e-7,polish=True)
    m0,p0=opt.x
    inner0=round((m0+1)*(1-p0)/(J-1))
    outer0=round((m0+1)*p0)
    best=None
    for inner in range(max(1,inner0-2),inner0+3):
        for outer in range(max(1,outer0-5),outer0+6):
            counts=[outer]+[inner]*(J-1)
            r=evaluate(sum(counts)-1,L,list(range(J)),counts)
            if r["E"] is not None and (best is None or r["E"]<best["E"]):
                best=r
    results.append(best)
    print(json.dumps(best),flush=True)
Path(__file__).with_name("extended_nested_search_2026-10-27.json").write_text(
    json.dumps({"floating_search_only":True,"rows":results},indent=2)+"\n",
    encoding="utf-8")
