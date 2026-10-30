module

public import OddPiPowers.Analysis.ActualContourBounds
public import OddPiPowers.Analysis.HorizontalMajorantIntegral

/-! Explicit whole-line bounds for the full factorial kernel on both sides. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem weightedHorizontalKernel_lower_integral_bound (hn : 0 < P.n) (theta Y : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖∫ t : ℝ, P.weightedHorizontalKernel h theta (-Y) t‖ ≤
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)) *
          ∫ t : ℝ, horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  have hi := P.integrable_weightedHorizontalKernel_lower hn theta Y hY m h hh hd
  have hg := (integrable_horizontalMajorant (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m).const_mul
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖))
  calc
    _ ≤ ∫ t : ℝ, ‖P.weightedHorizontalKernel h theta (-Y) t‖ := norm_integral_le_integral_norm _
    _ ≤ _ := (integral_mono hi.norm hg
      (fun t => P.weightedHorizontalKernel_lower_bound hn theta Y t hY m h hh hd)).trans_eq
        (integral_const_mul _ _)

theorem intervalFactorialProduct_norm :
    ‖P.intervalFactorialProduct‖ = ∏ a : Fin M, (Nat.factorial (P.length a) : ℝ) := by
  simp only [intervalFactorialProduct, norm_prod, Complex.norm_natCast]

theorem intervalFactorialProduct_norm_pos : 0 < ‖P.intervalFactorialProduct‖ := by
  rw [P.intervalFactorialProduct_norm]
  exact Finset.prod_pos (fun a ha => by exact_mod_cast Nat.factorial_pos (P.length a))

/-- The same scalar bounds both complete horizontal integrals. -/
noncomputable def centralLineBound (m h : ℕ) (theta Y : ℝ) : ℝ :=
  ‖P.intervalFactorialProduct‖ *
    (Real.exp (|theta| * ((P.n : ℝ) * Y)) *
      ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)) *
        (Real.pi * horizontalMajorantConstant (horizontalB Y) (Y + 1 / 2) m)

theorem centralLineBound_nonneg (m h : ℕ) (theta Y : ℝ) (hY : 1 / 2 < Y) :
    0 ≤ P.centralLineBound m h theta Y := by
  have hA := horizontalMajorantConstant_pos (B := horizontalB Y)
    (show 0 ≤ Y + 1 / 2 by linarith) m
  unfold centralLineBound
  positivity

theorem meromorphic_horizontal_integral_bound (hn : 0 < P.n) (theta Y : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖∫ t : ℝ, P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ))
      (horizontalPoint P.n Y t)‖ ≤ P.centralLineBound m h theta Y := by
  simp_rw [P.meromorphicExponentialKernel_horizontal]
  rw [integral_const_mul, norm_mul]
  have hb := P.weightedHorizontalKernel_integral_bound hn theta Y hY m h hh hd
  have hg := horizontalMajorant_integral_le (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m
  have hc : 0 ≤ Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
      ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖) := by positivity
  apply (mul_le_mul_of_nonneg_left
    (hb.trans (mul_le_mul_of_nonneg_left hg hc)) (norm_nonneg _)).trans_eq
  simp only [centralLineBound, abs_of_pos (show 0 < Y by linarith)]
  ring

theorem meromorphic_horizontal_lower_integral_bound (hn : 0 < P.n) (theta Y : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖∫ t : ℝ, P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ))
      (horizontalPoint P.n (-Y) t)‖ ≤ P.centralLineBound m h theta Y := by
  simp_rw [P.meromorphicExponentialKernel_horizontal]
  rw [integral_const_mul, norm_mul]
  have hb := P.weightedHorizontalKernel_lower_integral_bound hn theta Y hY m h hh hd
  have hg := horizontalMajorant_integral_le (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m
  have hc : 0 ≤ Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
      ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖) := by positivity
  apply (mul_le_mul_of_nonneg_left
    (hb.trans (mul_le_mul_of_nonneg_left hg hc)) (norm_nonneg _)).trans_eq
  simp only [centralLineBound, abs_of_pos (show 0 < Y by linarith)]
  ring

end ActualIntervals
end OddPiPowers
