"""Arb certificate for an arbitrary (L, offsets, counts), reusing code/certify.py.

Extension of ../certify_new.py.  The original code/certify.py is imported
unchanged; its certify() checks the Theorem 1.1 hypotheses (t_0=0, sorted
distinct offsets, 2 t_max < L, all nu_j >= 1, k odd >= 3), computes the exact
rational arc partition, Arb digamma weights, Arb saddle root by bisection,
and asserts G>0, gap>0, E < upper.

usage:
  python certify_any.py k L "o0,o1,..." "n0,n1,..." [upper]
  python certify_any.py --json ls_k3_L159.json [upper]
If upper is omitted it is the float estimate rounded UP to 2 decimals
(a float pre-estimate only; the Arb assertion is what certifies).
"""
import sys
import json
import math
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "code"))
from certify import certify  # noqa: E402


def float_estimate(k, L, offsets, counts):
    sys.path.insert(0, str(HERE))
    import numpy as np
    from cells import build, E_batch
    d = build(L, tuple(offsets))
    return float(E_batch(k, d, np.array(counts, dtype=float))["E"][0])


def main():
    args = sys.argv[1:]
    if args[0] == "--json":
        js = json.loads(Path(args[1]).read_text(encoding="utf-8"))
        k, L, offsets, counts = js["k"], js["L"], js["offsets"], js["counts"]
        rest = args[2:]
    else:
        k, L = int(args[0]), int(args[1])
        offsets = [int(x) for x in args[2].split(",")]
        counts = [int(x) for x in args[3].split(",")]
        rest = args[4:]
    if rest:
        upper = rest[0]
    else:
        e = float_estimate(k, L, offsets, counts)
        upper = f"{math.ceil(e * 100) / 100:.2f}"
        if float(upper) - e < 1e-6:          # guard exact ties of the rounding
            upper = f"{float(upper) + 0.01:.2f}"
        print(f"float estimate E={e:.10f} -> trying upper {upper}", flush=True)
    t0 = time.time()
    print(f"certifying k={k} L={L} offsets={offsets} counts={counts} upper={upper}", flush=True)
    row, _ = certify(k, L, offsets, counts, upper)
    row.pop("nonzero_merged_cells")
    row["seconds"] = round(time.time() - t0, 1)
    tag = f"k{k}_L{L}_m{row['m']}_n{len(offsets)}"
    out = HERE / f"cert_{tag}.json"
    out.write_text(json.dumps(row, indent=2) + "\n", encoding="utf-8")
    print(f"k={k} L={L} offsets={offsets} counts={counts} m={row['m']}")
    for key in ("Y", "D0", "G0", "gamma", "D", "G", "gap"):
        print(f"{key} = {row[key]}")
    print("E =", row["E"], "<", upper, " CERTIFIED", flush=True)
    print(f"json: {out}  ({row['seconds']}s)")


if __name__ == "__main__":
    main()
