module

public import OddPiPowers.Analysis.ActualRectangleContour
public import OddPiPowers.Analysis.HorizontalLineLimits

/-! Opening the actual finite contour to two infinite horizontal lines,
with scale fixed during truncation and with the exact Jacobian n. -/

@[expose] public section

namespace OddPiPowers

open Filter MeasureTheory
open scoped Topology

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem finitePoleContour_eq_horizontal (h : Fin M) (hM : 0 < M) (hn : 0 < P.n)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (m : ℕ) (hh : h.val ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    P.finitePoleContour h.val (Complex.I * (theta : ℂ)) =
      (P.n : ℂ) *
        ((∫ t : ℝ, P.meromorphicExponentialKernel h.val (Complex.I * (theta : ℂ))
          (horizontalPoint P.n (-Y) t)) -
         (∫ t : ℝ, P.meromorphicExponentialKernel h.val (Complex.I * (theta : ℂ))
          (horizontalPoint P.n Y t))) := by
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hY0 : 0 < Y := by linarith
  have hH : 0 < (P.n : ℝ) * Y := mul_pos hnR hY0
  have heq : ∀ᶠ R : ℝ in atTop,
      rectangleIntegral (P.meromorphicExponentialKernel h.val (Complex.I * (theta : ℂ)))
        (-R) R (-((P.n : ℝ) * Y)) ((P.n : ℝ) * Y) =
          P.finitePoleContour h.val (Complex.I * (theta : ℂ)) := by
    filter_upwards [eventually_gt_atTop (P.n : ℝ)] with R hR
    exact P.meromorphicExponentialKernel_rectangle_eq_finitePoleContour h hM _ _ _ _ _
      (by linarith) (by linarith) (by linarith) hH
  have hc : Tendsto (fun R : ℝ =>
      rectangleIntegral (P.meromorphicExponentialKernel h.val (Complex.I * (theta : ℂ)))
        (-R) R (-((P.n : ℝ) * Y)) ((P.n : ℝ) * Y)) atTop
      (𝓝 (P.finitePoleContour h.val (Complex.I * (theta : ℂ)))) :=
    tendsto_const_nhds.congr' (Filter.Eventually.mono heq (fun R he => he.symm))
  exact tendsto_nhds_unique hc
    (P.kernel_rectangle_tendsto_normalized hn theta Y hY m h.val hh hd)

end ActualIntervals

theorem actualExponentialRemainder_eq_horizontal {M : ℕ} (P : ActualIntervals M)
    (h : Fin M) (hM : 0 < M) (hn : 0 < P.n) (theta Y : ℝ) (hY : 1 / 2 < Y)
    (m : ℕ) (hh : h.val ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    actualExponentialRemainder P h (Complex.I * (theta : ℂ)) =
      (((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)) * (P.n : ℂ) *
        ((∫ t : ℝ, P.meromorphicExponentialKernel h.val (Complex.I * (theta : ℂ))
          (horizontalPoint P.n (-Y) t)) -
         (∫ t : ℝ, P.meromorphicExponentialKernel h.val (Complex.I * (theta : ℂ))
          (horizontalPoint P.n Y t))) := by
  rw [actualExponentialRemainder_eq_finitePoleContour P h hM,
    P.finitePoleContour_eq_horizontal h hM hn theta Y hY m hh hd]
  ring

theorem lambda_eq_I_mul_pi_div_two : lambda = Complex.I * (((Real.pi / 2 : ℝ) : ℂ)) := by
  unfold lambda
  push_cast
  ring

theorem actualAuxiliaryAtI_eq_horizontal {M : ℕ} (P : ActualIntervals M)
    (h : Fin M) (hM : 0 < M) (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (m : ℕ) (hh : h.val ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    (∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * lambda ^ j.val) =
      (((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)) * (P.n : ℂ) *
        ((∫ t : ℝ, P.meromorphicExponentialKernel h.val lambda (horizontalPoint P.n (-Y) t)) -
         (∫ t : ℝ, P.meromorphicExponentialKernel h.val lambda (horizontalPoint P.n Y t))) := by
  have ht := actualExponentialRemainder_eq_horizontal P h hM hn (Real.pi / 2) Y hY m hh hd
  rw [← lambda_eq_I_mul_pi_div_two] at ht
  simpa only [actualExponentialRemainder, exp_lambda_eq_I] using ht

theorem actualAuxiliaryAtI_norm_le_horizontal {M : ℕ} (P : ActualIntervals M)
    (h : Fin M) (hM : 0 < M) (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (m : ℕ) (hh : h.val ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * lambda ^ j.val‖ ≤
      ‖((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)‖ * (P.n : ℝ) *
        (‖∫ t : ℝ, P.meromorphicExponentialKernel h.val lambda (horizontalPoint P.n (-Y) t)‖ +
         ‖∫ t : ℝ, P.meromorphicExponentialKernel h.val lambda (horizontalPoint P.n Y t)‖) := by
  rw [actualAuxiliaryAtI_eq_horizontal P h hM hn Y hY m hh hd,
    norm_mul, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _)
    (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg P.n))

end OddPiPowers
