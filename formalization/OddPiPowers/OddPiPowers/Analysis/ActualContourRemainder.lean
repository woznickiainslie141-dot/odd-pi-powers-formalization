module

public import OddPiPowers.Analysis.ActualPoleContour
public import OddPiPowers.Transfer.AuxiliaryFamily

/-! Exact normalization of the finite contour to the actual auxiliary row,
including the specialization exp(i*pi/2)=i. -/

@[expose] public section

namespace OddPiPowers

theorem contourExponential_at_pole (lambda : ℂ) (n pole : ℕ) :
    contourExponential lambda n (-(pole : ℂ)) =
      Complex.exp (lambda * ((n : ℂ) - (pole : ℂ))) := by
  unfold contourExponential
  congr 1
  ring

theorem actualExponentialRemainder_commonScale {M : ℕ} (P : ActualIntervals M)
    (h : Fin M) (lambda : ℂ) :
    actualExponentialRemainder P h lambda =
      ((auxiliaryCommonScale M P.n : ℚ) : ℂ) *
        ∑ pole ∈ Finset.range (P.n + 1), ∑ j : Fin M,
          ((P.localCoefficient pole h.val j.val : ℚ) : ℂ) *
            (contourExponential lambda P.n (-(pole : ℂ)) * lambda ^ j.val /
              (Nat.factorial j.val : ℂ)) := by
  rw [actualExponentialRemainder_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pole hpole
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hs : ((auxiliaryScale M P.n j.val : ℚ) : ℂ) =
      ((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (Nat.factorial j.val : ℂ) := by
    change ((auxiliaryCommonScale M P.n / (Nat.factorial j.val : ℚ) : ℚ) : ℂ) = _
    push_cast
    rfl
  rw [contourExponential_at_pole]
  push_cast
  rw [hs]
  ring

/-- Exact actual-remainder/contour identity. The right side is a finite sum
of genuine complex line integrals, not a definition by a residue sum. -/
theorem actualExponentialRemainder_eq_finitePoleContour {M : ℕ}
    (P : ActualIntervals M) (h : Fin M) (hM : 0 < M) (lambda : ℂ) :
    actualExponentialRemainder P h lambda =
      (((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)) *
        P.finitePoleContour h.val lambda := by
  rw [P.finitePoleContour_eq_derivativeSum h hM,
    ← mul_assoc, div_mul_cancel₀ _ Complex.two_pi_I_ne_zero]
  exact actualExponentialRemainder_commonScale P h lambda

theorem exp_lambda_eq_I : Complex.exp lambda = Complex.I := by
  have he : lambda = (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold lambda
    push_cast
    ring
  rw [he, Complex.exp_mul_I]
  simp

theorem actualAuxiliaryAtI_eq_finitePoleContour {M : ℕ}
    (P : ActualIntervals M) (h : Fin M) (hM : 0 < M) :
    (∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * lambda ^ j.val) =
      (((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)) *
        P.finitePoleContour h.val lambda := by
  simpa only [actualExponentialRemainder, exp_lambda_eq_I] using
    actualExponentialRemainder_eq_finitePoleContour P h hM lambda

end OddPiPowers
