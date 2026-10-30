"""Two-level family nu=(a, b x T) scan of E_k for a list of L (float search).

usage: python scan2.py k L1 L2 ...   -> appends results to scan2_results.jsonl
"""
import sys
import json
import time
import numpy as np
from common import build, eval_many, tmax_for


def scan(k, L, amin=20, amax=140):
    Tmax = tmax_for(L)
    offs = tuple(range(Tmax + 1))
    t0 = time.time()
    data = build(L, offs)
    n = len(offs)
    bmax = max(4, int(np.ceil(900 / L)))
    Tlo = max(1, int(0.12 * L))
    cols, meta = [], []
    for T in range(Tlo, Tmax + 1):
        for b in range(1, bmax + 1):
            for a in range(amin, amax + 1):
                nu = np.zeros(n)
                nu[0] = a
                nu[1:T + 1] = b
                cols.append(nu)
                meta.append((a, b, T))
    r = eval_many(k, data, cols)
    order = np.argsort(r["E"])
    top = []
    for i in order[:12]:
        a, b, T = meta[i]
        top.append(dict(E=float(r["E"][i]), a=a, b=b, T=T, m=int(r["m"][i]),
                        D=float(r["D"][i]), G=float(r["G"][i]), gamma=float(r["gamma"][i]),
                        D0=float(r["D0"][i]), G0=float(r["G0"][i])))
    # boundary warning
    best = top[0]
    warn = []
    if best["a"] in (amin, amax):
        warn.append("a at boundary")
    if best["b"] == bmax:
        warn.append("b at boundary")
    if best["T"] in (Tlo, Tmax):
        warn.append("T at boundary")
    res = dict(k=k, L=L, Tmax=Tmax, ncols=len(cols), secs=time.time() - t0, top=top, warn=warn)
    return res


if __name__ == "__main__":
    k = int(sys.argv[1])
    for L in map(int, sys.argv[2:]):
        res = scan(k, L)
        with open(f"scan2_k{k}_results.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(res) + "\n")
        b = res["top"][0]
        print(f"L={L}: E={b['E']:.4f} a={b['a']} b={b['b']} T={b['T']} m={b['m']} "
              f"({res['ncols']} cols, {res['secs']:.0f}s) {res['warn']}", flush=True)
