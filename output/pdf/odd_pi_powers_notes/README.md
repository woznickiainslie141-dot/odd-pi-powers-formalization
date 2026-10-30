# Explicit irrationality bounds for odd powers of pi

Expanded English research notes, dated 27 October 2026.
No priority, record, global optimality, or bound below 100 is claimed.

## Main result

The nested logarithmic Hermite-Pade system gives

    mu(pi^k) <= m(D0+G0)/(D0-(k-1)G0+k*gamma)

when its gap is positive. Explicit twelve-layer choices give

    mu(pi^3) < 1203.973
    mu(pi^5) < 42461
    mu(pi^7) < 1272103
    mu(pi^9) < 35398937.

A root-free parameter recipe applies to every fixed odd k >= 3.

## Contents

- main.tex and sections/: editable manuscript.
- main.pdf: compiled manuscript.
- code/certify.py: standalone exact arc partition and Arb certificates.
- data/certificates.json: rate enclosures and all merged arc cells.
- code/finite_checks.py: exact small polynomial and divisor checks.
- data/finite_checks.json and data/toy_matrix.tex: check output.
- code/experiment_arcsin.py and code/experiment_beta3.py: optional finite experiments.
- data/experiment_*.json: experiment output.

## Reproduce

The certificate requires Python 3 and python-flint.
The symbolic checks additionally require sympy.
Optional experiments additionally require mpmath.
NumPy and SciPy are not required by this source package.

From this directory:

    python code/certify.py
    python code/finite_checks.py
    xelatex -interaction=nonstopmode -halt-on-error main.tex
    xelatex -interaction=nonstopmode -halt-on-error main.tex

The certificate proves strict numerical comparisons. The manuscript
proves the algebraic and analytic lemmas, including the infinite contour
tails and minimal-polynomial transfer. The prime number theorem is an
external classical input. Finite experiments do not prove asymptotics.

The notes do not tabulate explicit denominator thresholds q0(epsilon)
or numerical constants in the rational-approximation lower bounds.
