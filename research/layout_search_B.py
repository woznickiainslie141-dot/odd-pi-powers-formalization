"""B-lite: local search over nested layouts (offsets t_j, multiplicities nu_j)
using the exact-arc gamma evaluator.  Floating-point search only; any hit would
still need the Arb certificate and G>=0 / gap>0 checks (enforced here)."""
import sys
import time
import random
import json
from pathlib import Path
import numpy as np
from search_multilayer_pade import evaluate

K = 3


def score(L, offsets, counts):
    if len(set(offsets)) != len(offsets) or min(offsets) != 0:
        return None
    if max(offsets) * 2 >= L:
        return None
    m = sum(counts) - 1
    try:
        r = evaluate(m, L, tuple(offsets), counts)
    except AssertionError:
        return None
    if r["E"] is None or r["G0"] - r["gamma"] < 0:
        return None
    return r["E"], r


if __name__ == "__main__":
    t0 = time.time()
    base = score(69, tuple(range(12)), [66] + [11] * 11)
    print("baseline", base[0], "time", time.time() - t0, flush=True)
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    random.seed(20261027)
    best = (base[0], 69, list(range(12)), [66] + [11] * 11)
    start = time.time()
    it = 0
    while time.time() - start < budget:
        it += 1
        E, L, off, cnt = best
        off = list(off)
        cnt = list(cnt)
        move = random.choice(["count", "count", "shift", "add", "drop", "L"])
        if move == "count":
            i, j = random.sample(range(len(cnt)), 2) if len(cnt) > 1 else (0, 0)
            d = random.choice([1, 2, 3, 5])
            if cnt[i] > d:
                cnt[i] -= d
                cnt[j] += d
        elif move == "shift":
            i = random.randrange(1, len(off)) if len(off) > 1 else 0
            if i:
                off[i] += random.choice([-1, 1])
        elif move == "add":
            free = [t for t in range(1, (L - 1) // 2 + 1) if t not in off]
            if free:
                off.append(random.choice(free))
                cnt.append(random.choice([1, 2, 3]))
        elif move == "drop" and len(off) > 3:
            i = random.randrange(1, len(off))
            cnt[0] += cnt[i]
            del off[i], cnt[i]
        elif move == "L":
            L += random.choice([-2, -1, 1, 2])
        order = np.argsort(off)
        off = [off[i] for i in order]
        cnt = [cnt[i] for i in order]
        r = score(L, tuple(off), cnt)
        if r and r[0] < best[0] - 1e-9:
            best = (r[0], L, off, cnt)
            print(f"it={it} E={r[0]:.3f} m={sum(cnt)-1} L={L} off={off} cnt={cnt}",
                  flush=True)
    E, L, off, cnt = best
    out = {"E": E, "L": L, "offsets": off, "counts": cnt, "m": sum(cnt) - 1,
           "iterations": it, "note": "floating-point local search, uncertified"}
    Path(__file__).with_name("layout_search_B_2026-10-27.json").write_text(
        json.dumps(out, indent=1))
    print(json.dumps(out))
