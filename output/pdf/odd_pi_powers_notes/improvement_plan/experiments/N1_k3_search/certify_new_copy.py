"""Arb certificates for new parameter choices, reusing code/certify.py.

usage: python certify_new.py k L T a b upper   (offsets 0..T, nu=(a,b,...,b))
The analytic hypotheses are those of Theorem 1.1 (nested symmetric
intervals, t_0=0, all nu_j>=1), which these shapes satisfy.
"""
import sys
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code"))
from certify import certify  # noqa: E402

k, L, T, a, b = map(int, sys.argv[1:6])
upper = sys.argv[6]
offsets = list(range(T + 1))
counts = [a] + [b] * T
row, _ = certify(k, L, offsets, counts, upper)
row.pop("nonzero_merged_cells")
out = Path(__file__).with_name(f"cert_k{k}_L{L}_T{T}_a{a}_b{b}.json")
out.write_text(json.dumps(row, indent=2) + "\n", encoding="utf-8")
print(f"k={k} L={L} T={T} nu=({a},{b}x{T}) m={row['m']}")
print("E =", row["E"], "<", upper, " CERTIFIED")
