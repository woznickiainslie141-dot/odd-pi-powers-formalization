# Explicit irrationality bounds for odd powers of pi

Expanded English research notes, revised **31 October 2026**. The general
transfer also applies to even integer powers. No priority, record, global
optimality, or cubic bound below 100 is claimed.

## Latest accepted result

    mu(pi^3) <= 12970477737/11706979
              = 1107.9269670681... < 1107.93.

This L99 instance uses 28 interval types, multiplicities (64,4,...,4),
degree 171, rational height 1801/20, and conservative rational rates
D=54469491/100000 and G=2672657/12500. The actual auxiliary family and
fixed final theorem have accepted Lean build and transitive axiom evidence.
See ../../../formalization/L99_CURRENT_CHECKPOINT.md and the canonical
executed report in ../../../formalization/OddPiPowers/logs/.

## Scope and comparisons

The parameter formula is

    mu(pi^k) <= m(D+G)/(D-(k-1)G),  k>=2,

provided G>=0 and the gap is positive. It has no parity restriction.
The expanded notes distinguish the following verification levels:

| Result | Status |
|---|---|
| General integer-power transfer | Accepted Lean theorem |
| L99 cubic exact bound above | Accepted fixed Lean application |
| Older twelve-layer cubic bound below 1203.973 | Accepted fixed Lean application, with a slightly conservative exact constant |
| Twelve-layer k=5,7,9 bounds 42461,1272103,35398937 | Manuscript proofs plus original Arb certificates |
| L99 k=4, scale 19, expression below 6628.70 | Manuscript specialization plus fresh Arb comparison; no fixed Lean acceptance |
| Uniform bound 301*8^k for k>=3 | Paper-level proof; no all-k Lean acceptance |

A detailed specialization of Nesterenko--Waldschmidt gives the older bound
1200000*k*(1+log(k)). It already beats the displayed twelve-layer k=9
number. For pi^4 the specialized Marcovecchio--Zudilin bound is
12.51085940..., much better than this construction's fourth-power example.
These notes do not claim an exhaustive current-record survey.

## Reading and files

- main.tex, sections/: editable source, including background, literature,
  L99 calculations, formalization guide, notation, and exercises.
- main.pdf: compiled revised manuscript.
- ../odd_pi_powers_notes.pdf: identical delivery copy.
- ../odd_pi_powers_notes_source.zip: standalone manuscript source package;
  includes a copy of the acceptance report, not the complete Lean project.
- code/certify.py and data/certificates.json: original odd-power Arb table.
- code/check_current_results.py: revised exact ledger and Arb comparisons.
- data/current_results_2026-10-31.json: fresh numerical output.
- data/l99_acceptance_report_2026-10-31.json: bundled copy of the executed
  earlier Lean acceptance report; copying it does not constitute a rebuild.
- code/finite_checks.py and data/finite_checks.json: exact small examples.
- code/experiment_*.py and data/experiment_*.json: optional finite searches.
- REVISION_2026-10-31.md: changes and validation for this editorial revision.

## Reproduce

Python 3 and python-flint are required for the numerical comparisons.
The small symbolic examples additionally require SymPy. Optional searches
require mpmath. NumPy and SciPy are not required.

From this directory:

    python code/check_current_results.py
    python code/certify.py
    python code/finite_checks.py
    xelatex -interaction=nonstopmode -halt-on-error main.tex
    xelatex -interaction=nonstopmode -halt-on-error main.tex

The English manuscript also supports pdfLaTeX. Numerical programs certify
their stated comparisons; they do not prove every analytic lemma or run
Lean. The full pinned Lean source and bounded build instructions remain in
the workspace formalization project. Accepted Lean sources and toolchain
are unchanged by this manuscript revision.

The notes make the exponent explicit. They do not tabulate numerical
q0(epsilon) or c_epsilon for the nested construction. The classical
Nesterenko--Waldschmidt consequence has its own displayed explicit prefactor.
