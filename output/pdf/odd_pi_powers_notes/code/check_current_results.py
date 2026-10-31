"""Check the revised manuscript's arithmetic; this does not run Lean.

The bundled executed acceptance report is evidence from the previous Lean
run, not a replacement for rebuilding its source dependency closure.
Only rational arithmetic and 256-bit Arb comparisons are performed here.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

from flint import arb, ctx

ctx.prec = 256
PROJECT = Path(__file__).resolve().parents[1]
DATA = PROJECT / "data"
REPORT = DATA / "l99_acceptance_report_2026-10-31.json"


def ball(q):
    q = F(q)
    return arb(q.numerator) / q.denominator


def main():
    report = json.loads(REPORT.read_text(encoding="utf-8"))
    assert report["status"] == "accepted"
    assert report["bound"] == "12970477737/11706979"
    params = report["fixed_parameters"]
    assert params["counts"] == [64] + [4] * 27
    assert params["offsets"] == list(range(28))
    assert params["m"] == 171 and params["Y"] == "1801/20"
    D, G = F(params["D"]), F(params["G"])
    gamma = F(params["gamma"])
    E = 171 * (D + G) / (D - 2 * G)
    assert E == F(report["bound"]) and E < F(110793, 100)
    rounding_margin = 110793 * E.denominator - 100 * E.numerator
    assert rounding_margin == 3550647
    assert D - 3 * G == F(-9674277, 100000)

    weights = [16] + [1] * 27
    lengths = [F(99 - 2 * j, 99) for j in range(28)]
    S = sum((nu * c for nu, c in zip(weights, lengths)), F(0))
    assert S == F(389, 11) and sum(weights) == 43
    theta = arb.pi() / 2
    Y = ball(F(params["Y"]))
    D0 = sum((4 * nu * (ball(c) / 2 *
              ((1 + (2 * Y / ball(c)) ** 2) / 4).log()
              + 2 * Y * (ball(c) / (2 * Y)).atan())
              for nu, c in zip(weights, lengths)), arb(0)) - theta * Y - 171
    G0 = 171 + ball(4 * S) * arb(2).log()
    assert D0 > ball(F(9789173, 20000))
    assert G0 < ball(F(13452441, 50000))
    assert F(9789173, 20000) + gamma == D
    assert F(13452441, 50000) - gamma == G

    prefix = F(1380525198339888, 10 ** 14)
    tail = F(381339545481, 10 ** 14)
    shrink_loss = F(2 * 99 ** 2 * 1000000 * 43 * 3004, 99 * 10 ** 56)
    gamma0 = gamma / 4
    assert prefix + tail - shrink_loss > gamma0
    A = sum((nu * ball(c) * ball(c).log()
             for nu, c in zip(weights, lengths)), arb(0))
    g = 43 + ball(S) * arb(2).log() - ball(gamma0)
    d = ball(S) * (ball(S) / theta).log() - A - 43 + ball(gamma0)
    assert g > 1 and g < 60 and d > 0

    s, k, m = 19, 4, 816
    lower_D = s * (ball(S) * arb(s).log() + d) + 1 - theta ** 2 / (12 * s * ball(S))
    growth = s * g - 1
    gap = lower_D - (k - 1) * growth
    fourth_E = m * (lower_D + growth) / gap
    assert gap > 0 and fourth_E < ball(F(662870, 100))
    result = {
        "revision_date": "2026-10-31",
        "scope": "Rational and Arb checks for the revised manuscript; no new Lean run",
        "acceptance_report_sha256": hashlib.sha256(REPORT.read_bytes()).hexdigest(),
        "l99_accepted": {
            "E": str(E), "E_decimal_ball": str(ball(E)),
            "rounding_cross_product_margin": rounding_margin,
            "D0_at_rational_height": str(D0), "G0": str(G0),
            "old_scale_fourth_power_gap": str(D - 3 * G),
            "base_gamma_lower": str(gamma0),
            "finite_window_margin_after_loss": str(prefix + tail - shrink_loss - gamma0),
        },
        "fourth_power_root_free": {
            "status": "Manuscript specialization plus Arb; not an accepted fixed Lean instance",
            "k": k, "s": s, "m": m, "S": str(S),
            "g": str(g), "d": str(d), "D_lower": str(lower_D),
            "G": str(growth), "gap": str(gap), "E": str(fourth_E),
            "strict_upper": "6628.70",
        },
        "classical_comparison": [
            {"k": k, "B(k)": str(1200000 * k * (1 + arb(k).log()))}
            for k in (3, 5, 7, 9)
        ],
        "uniform_all_power": {
            "status": "Paper proof; this finite program does not prove a universal quantifier",
            "bound": "301*8^k for every integer k>=3",
            "constant_checks": "1<g<60 and d>0 enclosed by Arb; paper gives elementary proofs",
        },
    }
    (DATA / "current_results_2026-10-31.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("L99 exact exponent:", E)
    print("Strict rounding margin:", rounding_margin)
    print("Fourth-power root-free expression:", fourth_E, "<6628.70")
    print("All revised-manuscript arithmetic comparisons passed.")


if __name__ == "__main__":
    main()
