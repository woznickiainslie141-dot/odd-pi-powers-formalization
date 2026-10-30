module

public import OddPiPowers.Transfer.DividedDifference
public import OddPiPowers.Transfer.NonzeroRow
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Exact input interface for the abstract transfer theorem. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

noncomputable def lambda : ℂ := Complex.I * (Real.pi : ℂ) / 2

noncomputable def complexPolynomial (u : GaussianInt[X]) : ℂ[X] :=
  u.map GaussianInt.toComplex

noncomputable def complexDividedDifference (m : ℕ) (u : GaussianInt[X]) : ℂ[X] :=
  dividedDifference m (complexPolynomial u).coeff lambda

theorem complexPolynomial_eval_sub (m : ℕ) (u : GaussianInt[X]) (hu : u.natDegree ≤ m)
    (y : ℂ) : (complexPolynomial u).eval lambda - (complexPolynomial u).eval y =
      (lambda - y) * (complexDividedDifference m u).eval y := by
  apply polynomial_eval_sub
  simpa only [complexPolynomial, natDegree_map_eq_of_injective GaussianInt.toComplex_injective]
    using hu

/-- The only hypotheses to be supplied by the nested construction. The
threshold is uniform in every row and every point of the closed disk. Rates
are normalized by `n = L*r`, with all parameters fixed before `r → ∞`. -/
structure AuxiliaryFamily (m L : ℕ) (D G : ℝ)
    (U : ℕ → Fin (m + 1) → GaussianInt[X]) : Prop where
  degree : ∀ r, 0 < r → ∀ i, (U (L * r) i).natDegree ≤ m
  determinant : ∀ r, 0 < r → (coefficientMatrix m (U (L * r))).det ≠ 0
  bounds : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ r, 0 < r → N ≤ L * r →
    (∀ i, ‖(complexPolynomial (U (L * r) i)).eval lambda‖ ≤
      Real.exp (-(D - η) * (L * r : ℕ))) ∧
    (∀ i z, ‖z‖ ≤ 2 → ‖(complexPolynomial (U (L * r) i)).eval z‖ ≤
      Real.exp ((G + η) * (L * r : ℕ))) ∧
    (∀ i z, ‖z‖ ≤ 2 → ‖(complexDividedDifference m (U (L * r) i)).eval z‖ ≤
      Real.exp ((G + η) * (L * r : ℕ)))

end OddPiPowers
