"""Arb certificate for arbitrary multiplicity lists, reusing code/certify.py.

(Extension of ../certify_new.py; code/certify.py is imported read-only.)
usage: python certify_any.py k L nu_csv upper [tag]
  offsets are 0..len(nu)-1 (contiguous, t_0=0), counts = nu (all >= 1).
The analytic hypotheses are those of Theorem 1.1 (nested symmetric
intervals, t_0 = 0, 2 t_max < L, all nu_j >= 1); certify() asserts them.
"""
import sys
import json
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "code"))
from certify import certify  # noqa: E402

k, L = int(sys.argv[1]), int(sys.argv[2])
counts = [int(x) for x in sys.argv[3].split(",")]
upper = sys.argv[4]
tag = sys.argv[5] if len(sys.argv) > 5 else f"k{k}_L{L}"
offsets = list(range(len(counts)))
t0 = time.time()
row, _ = certify(k, L, offsets, counts, upper)
row.pop("nonzero_merged_cells")
row["seconds"] = round(time.time() - t0, 1)
out = Path(__file__).with_name(f"cert_{tag}.json")
out.write_text(json.dumps(row, indent=1) + "\n", encoding="utf-8")
print(f"k={k} L={L} T={len(counts)-1} nu={counts} m={row['m']}")
print("E =", row["E"], "<", upper, " CERTIFIED", f"({row['seconds']}s)")
