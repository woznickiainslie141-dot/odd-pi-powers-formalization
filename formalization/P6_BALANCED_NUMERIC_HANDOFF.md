# P6 balanced-family numeric draft handoff

`OddPiPowers/Analysis/BalancedNumericCertificate.lean` is an **uncompiled
draft**. The helper ran no Lean, Lake, bounded runner, build, generator or
axiom audit and modified no existing Lean source, root, scripts, manifest or
cache. Main exclusively owns compilation, integration and acceptance.

For the proposed balanced all-pole instance `M=512`, `m=511`, `Y=128`, the
draft defines

    balancedD0 = 512 * centralIntervalRate 1 128 - (pi/2)*128 - 511
    balancedG0 = 511 + 512*log 2

and attempts ordinary proofs of `balancedD0 ≥ 2000`, `balancedG0 ≤ 900`,
`0 < 2000 - 2*900`, and
`511*(2000+900) < 7500*(2000-2*900)`. Mathematically the comparison gives
the coarse rational target 7500 **only after** main proves the actual
balanced family and applies the accepted transfer theorem. This is a first
milestone; it does not establish the P6 goal below 1203973/1000.

The proof uses source-verified Mathlib bounds
`Real.le_log_one_add_of_nonneg`, `Real.log_two_lt_d9`, `Real.pi_le_four`,
`Real.log_pow`, the global theorem `integral_one_div_one_add_sq`, and
`intervalIntegral.integral_mono_on`. For the lower arctangent bound, compare
`1/(1+x²)` with `3/4` on `[0,1/256]` and integrate. Monotonicity of log
then gives `centralIntervalRate 1 128 ≥ log 128 + 3/4` and
`log 128 = 7 log 2`. The resulting lower estimate is actually
`512*(65/12)-256-511 = 2006⅓`, leaving margin above 2000.

The draft's imports `Mathlib.Analysis.Complex.ExponentialBounds` and
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic` are present as Mathlib
sources, but **their compiled cache availability and aggregate import cost
were not checked**. `Real.log_two_lt_d9` is a Mathlib theorem with an ordinary
source proof, not an external numerical output. If either module is absent
from the preserved cache or exceeds the bound, main must use the permitted
guarded workflow and split the proof; never run an unguarded dependency build.
An alternate upper bound `log 2 ≤ 5/6` follows from elementary log estimates,
but changes the rate bound and requires recomputing a coarser rational target.

Likely compiler repairs: elaboration of `integral_mono_on` and its constant
integrability type; simplification of the definite integral and `arctan 0`;
`norm_num` normalization before `linarith` in the `log 128` and central-rate
lemmas; local `fun_prop`/`positivity` imports and exact `Real.log_le_log`
arguments; and namespace or simplifier details for the stated integral
formula. The lower log lemma is also directly available as
`Real.log_two_gt_d9` if the `le_log_one_add_of_nonneg` specialization needs
repair. Evaluate proof cost under the prescribed bounded runner.

No new mathematical axiom, `sorry`, `admit`, or native evaluation is used in
the draft. Uniform heights, Gaussian row validation, actual family assembly,
sharp divisor and the required final numerical pi³ bound remain open.
