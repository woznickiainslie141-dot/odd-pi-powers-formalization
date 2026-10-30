"""Certified numerical evaluations for the pi-powers research roadmap.

Requires python-flint. Arb ball arithmetic certifies the stated comparisons;
it does not prove the analytic estimates or optimality of the chosen m.
Run from any directory: python research/pi_powers_route_certificate.py
"""
from pathlib import Path
import json
from flint import arb, ctx

ctx.prec = 256


def rates(m):
    M = arb(m + 1)
    D = -M * (2 * (arb.pi() / (4 * M)).sin()).log() - m
    G = arb(m) + M * arb(2).log()
    return D, G


rows = []
for k, m, upper in [
    (3, 289, "2028.145383"),
    (5, 9196, "95404"),
    (7, 278685, "3840228"),
    (9, 8356506, "143565918"),
]:
    D, G = rates(m)
    gap = D - (k - 1) * G
    assert gap > 0
    E = m * (D + G) / gap
    assert E < arb(upper)
    rows.append({
        "k": k, "m": m, "D": str(D), "G": str(G),
        "gap": str(gap), "E": str(E),
        "certified_strict_upper": upper,
        "globally_optimal_m_claimed": False,
    })

D, G = rates(289)
gamma_threshold = (289 * (D + G) / 2000 - (D - 2 * G)) / 3
gamma = arb(23) / 20
conditional_E = 289 * (D + G) / (D - 2 * G + 3 * gamma)
assert gamma_threshold < gamma
assert conditional_E < arb("1999.901")

data = {
    "arithmetic": "Arb real balls; 256 bits",
    "scope": "Numerical comparisons only; no new common divisor is asserted.",
    "table": rows,
    "conditional_pi3_improvement": {
        "m": 289, "target": 2000,
        "gamma_threshold": str(gamma_threshold),
        "hypothetical_gamma": "23/20",
        "conditional_E": str(conditional_E),
        "certified_strict_upper": "1999.901",
    },
}
out = Path(__file__).with_name("pi_powers_route_certificate.json")
out.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
               encoding="utf-8")
print(json.dumps(data, ensure_ascii=False, indent=2))
