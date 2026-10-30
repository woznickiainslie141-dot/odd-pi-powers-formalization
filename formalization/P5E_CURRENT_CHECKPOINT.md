# P5-E accepted checkpoint

P5-E and the bounded P6-A certificate-soundness bridge are accepted.
Read P5E_REVIEW_2026-10-29.md and P5E_MATHEMATICAL_NOTES.md.
No compiler remains running. The current assigned bounded work is complete.

P1 through P5-D and P5-E are accepted. The actual central Stirling/Riemann
rate is now proved, including endpoints, common normalization and uniform
actual/reduced-row exponential bounds for every fixed Y>1/2. The seventeen
base rows are instantiated. Generic fixed integer endpoint families are
also covered. P6-A rational certificate soundness is accepted, retaining
the full AuxiliaryFamily explicitly as a hypothesis.

Complete validation: 151 modules, 3 executed
targets and 148 verified records, fresh complete
root (4010 jobs), 50 new and 471 prior axiom checks. Only propext,
Classical.choice and Quot.sound occur. Fresh audit peak 5144.55 MiB under
the unchanged 6144 MiB cap. All 139 prior mathematical sources are unchanged.
See formalization/P5E_REVIEW_2026-10-29.md and
formalization/P5E_CURRENT_CHECKPOINT.md (workspace-relative paths).

P6 is not numerically closed. For the fastest first closed instance, use
the balanced all-pole family, unreduced coefficients and a fixed rational
height; its height proof avoids regular factors and improved gamma.
For the manuscript target: explicit s=11, M=187 actual family and
grouping for the pi^3 target; uniform coefficient heights and disk/difference
bounds; complete actual AuxiliaryFamily; sharp divisor rate and kernel-checked
pi/log/atan numeric certificates. The exact height APIs are recorded in
formalization/P5_HEIGHT_PROOF_PLAN.md. Optimal-height existence/uniqueness
is not a prerequisite.

All future Lean operations retain the mandatory memory contract. Main alone
owns compiler access. Preserve sources, v4.35.0, manifest, caches, D: storage,
C: junctions and paging settings. The helper has no compiler authority.
