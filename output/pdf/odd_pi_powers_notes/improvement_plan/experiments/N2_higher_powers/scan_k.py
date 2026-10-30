"""Two-level (+ fractional last layer) shape scan for E_k, k odd.

shape v = (1, w x T, lam*w); asymptotic screening, exact real-s minimisation
for the top candidates, then integer rounding + local search.
usage: python scan_k.py L Tmax k1,k2,...
"""
import sys
import json
import time
import math
import numpy as np
from hp import load, gamma_batch, shape_consts, asym_E, best_real_s, int_refine, two_level

L, Tmax = int(sys.argv[1]), int(sys.argv[2])
ks = [int(x) for x in sys.argv[3].split(",")]
t0 = time.time()
d = load(L, Tmax)
print(f"L={L} Tmax={Tmax} cells built ({time.time()-t0:.1f}s), rows={d['nrows']}", flush=True)

ws = np.exp(np.linspace(math.log(0.01), math.log(0.6), 120))
lams = [0.0, 0.25, 0.5, 0.75]
shapes = []
for T in range(1, Tmax):
    for lam in lams:
        for w in ws:
            shapes.append((T, w, lam))
NU = np.zeros((Tmax + 1, len(shapes)))
for i, (T, w, lam) in enumerate(shapes):
    v = two_level(T, w, lam)
    NU[:len(v), i] = v
G = np.concatenate([gamma_batch(d, NU[:, i:i + 2000]) for i in range(0, NU.shape[1], 2000)])
print(f"gamma for {len(shapes)} shapes ({time.time()-t0:.1f}s)", flush=True)
consts = [shape_consts(L, NU[:, i], G[i]) for i in range(len(shapes))]
rhos = np.array([c["rho"] for c in consts])
i = int(np.argmin(rhos))
print("best rho in family: %.6f at T=%d w=%.5f lam=%.2f" % (rhos[i], *shapes[i]), flush=True)

out = {"L": L, "Tmax": Tmax, "best_rho": [float(rhos[i]), list(map(float, shapes[i]))], "k": {}}
for k in ks:
    asy = np.array([asym_E(k, c)[0] for c in consts])
    order = np.argsort(asy)[:40]
    exact = []
    for j in order:
        T, w, lam = shapes[j]
        v = two_level(T, w, lam)
        r = best_real_s(k, L, v, G[j])
        exact.append((r["E"], j, r["s"]))
    exact.sort()
    print(f"k={k}: top real-s candidates", flush=True)
    for e, j, s in exact[:5]:
        T, w, lam = shapes[j]
        print(f"   E_real={e:.6f} T={T} w={w:.5f} lam={lam} s={s:.3f} rho={rhos[j]:.6f} asym={asy[j]:.4f}", flush=True)
    res = []
    for e, j, s in exact[:4]:
        T, w, lam = shapes[j]
        v = two_level(T, w, lam)
        Eint, nu = int_refine(k, d, v, s)
        res.append((Eint, nu.astype(int).tolist(), e, list(map(float, shapes[j]))))
    res.sort(key=lambda x: x[0])
    Eint, nu, e, sh = res[0]
    nz = [x for x in nu if x > 0]
    print(f"k={k}: best integer E={Eint:.6f} (real {e:.6f}) nu={nz[:3]}..{nz[-2:]} len={len(nz)} "
          f"({time.time()-t0:.1f}s)", flush=True)
    out["k"][str(k)] = [dict(E_int=r[0], nu=[x for x in r[1] if x > 0], E_real=r[2], shape=r[3]) for r in res]

with open(f"scan_L{L}.json", "w") as f:
    json.dump(out, f, indent=1)
