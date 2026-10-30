# P6 helper handoff: unreduced Gaussian rows

`OddPiPowers/Construction/GaussianAuxiliaryRows.lean` is an **uncompiled proof
draft**. The helper ran no Lean, Lake, bounded runner, build, generator, or
axiom audit. Main owns all compiler access and must repair, validate, integrate
and audit the module. No existing source, project root, scripts, manifest,
toolchain or cache was edited by this helper.

For each `P : ActualIntervals M` the draft defines
`gaussianAuxiliaryCoefficient P h j` by evaluating `actualAuxiliaryInt P h j`
at `gaussianI`, and `gaussianAuxiliaryRow P h` as the finite sum of those
coefficients times `X^j`. Candidate proofs provide:

* coefficient embedding into ℂ equals the rational actual polynomial evaluated
  at `Complex.I`, through `Polynomial.hom_eval₂` and the accepted
  `ActualIntervals.actualAuxiliaryInt_evalI`;
* coefficient extraction, row evaluation at an arbitrary complex `z`, and
  degree at most `M-1`;
* equality of the complex image of the Gaussian coefficient matrix with
  `actualAuxiliaryPolynomialMatrixAtI P`, and Gaussian determinant nonzero by
  the accepted complex determinant nonvanishing;
* direct degree and determinant statements matching
  `OddPiPowers.coefficientMatrix m` for `P : ActualIntervals (m+1)`.

The rows are unreduced: no common divisor, analytic representation, numerical
bound, or height hypothesis is introduced. The determinant result does not
depend on `M > 0`; the transfer-specific version uses `M=m+1`. The coefficient
definition agrees with the accepted integer lift, not a new rational choice.

Compiler risks: `Polynomial.hom_eval₂` argument inference and simp across the
composition of integer-cast ring homomorphisms; exact application of
`ActualIntervals.actualAuxiliaryIntEvalI` and `actualAuxiliaryInt_evalI`;
the direction of `Polynomial.coeff_C_mul_X_pow` equalities in the finite sum;
`natDegree_sum_le_of_forall_le` and `natDegree_C_mul_le` elaboration;
unfolding `RingHom.mapMatrix`, `actualAuxiliaryPolynomialEvalI`, and row
coefficient simplification; `RingHom.map_det` rewrite orientation; and
definitional equality between the `M=m+1` coefficient matrices. The draft
uses `omega` for `j.val ≤ M-1`, already used in the imported actual auxiliary
source; main should add a narrow tactic import only if needed.

To connect the accepted P5-C/P5-E remainder results, main should rewrite
`gaussianAuxiliaryRow_eval` at `z = Complex.I * (theta : ℂ)/2` and use the
existing row-at-`i` representation. This file alone does not prove the required
uniform disk height, divided-difference estimate, explicit scaled family,
complete `AuxiliaryFamily`, or any numerical irrationality bound. No `sorry`,
`admit`, new axiom, or native evaluation was added in the draft.
