import time, math, numpy as np
from continuum import Shape, gamma_cont, rho_of
tau, om = 0.28, 6.2
sh = Shape(1.0, [(0.0, tau, om)])
print("slopes", sh.slopes())
for X in (2e3, 5e3, 2e4, 5e4):
    t0 = time.time()
    g, info = gamma_cont(sh, X)
    print(f"X={X:.0e} gamma={g:.12f} rho={rho_of(sh,g):.10f} n={info['n_intervals']} Hmean={info['Hmean']:.4f} ({time.time()-t0:.1f}s)", flush=True)
for nsub in (False,):
    g, info = gamma_cont(sh, 2e4, split_crossings=False)
    print("no-split X=2e4", g)
