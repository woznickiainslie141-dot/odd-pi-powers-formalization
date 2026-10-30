module

public import OddPiPowers.Analysis.ActualHorizontalRepresentation
public import OddPiPowers.Analysis.WeightedHorizontalIntegral

/-! A non-asymptotic central estimate for every actual auxiliary row. -/

@[expose] public section

namespace OddPiPowers

theorem auxiliaryCommonScale_cast_pos (M n : ℕ) :
    0 < ((auxiliaryCommonScale M n : ℚ) : ℝ) := by
  unfold auxiliaryCommonScale
  push_cast
  have hF : (0 : ℝ) < Nat.factorial (M - 1) := by exact_mod_cast Nat.factorial_pos (M - 1)
  have hL : (0 : ℝ) < intervalLcm n := by exact_mod_cast intervalLcm_pos n
  positivity

theorem auxiliaryCommonScale_contour_norm (M n : ℕ) :
    ‖((auxiliaryCommonScale M n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)‖ =
      ((auxiliaryCommonScale M n : ℚ) : ℝ) / (2 * Real.pi) := by
  have hs : ((auxiliaryCommonScale M n : ℚ) : ℂ) =
      ((((auxiliaryCommonScale M n : ℚ) : ℝ)) : ℂ) := by norm_cast
  rw [hs]
  simp [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos (auxiliaryCommonScale_cast_pos M n)]

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

/-- After the two line constants cancel the contour's 2*pi, this is an
explicit scalar with no remaining improper integral. -/
noncomputable def centralRemainderBound (m h : ℕ) (theta Y : ℝ) : ℝ :=
  ((auxiliaryCommonScale M P.n : ℚ) : ℝ) *
    horizontalMajorantConstant (horizontalB Y) (Y + 1 / 2) m *
      (P.n : ℝ) ^ (h + 1) * Real.exp (|theta| * ((P.n : ℝ) * Y)) *
        ‖P.intervalFactorialProduct‖ / ‖P.horizontalDenominator Y 0‖

theorem centralRemainderBound_pos (hn : 0 < P.n) (m h : ℕ) (theta Y : ℝ)
    (hY : 1 / 2 < Y) : 0 < P.centralRemainderBound m h theta Y := by
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hQ := norm_pos_iff.mpr (P.horizontalDenominator_ne_zero hn Y 0 (by linarith))
  have hF := P.intervalFactorialProduct_norm_pos
  have hS := auxiliaryCommonScale_cast_pos M P.n
  have hA := horizontalMajorantConstant_pos (B := horizontalB Y)
    (show 0 ≤ Y + 1 / 2 by linarith) m
  unfold centralRemainderBound
  positivity

theorem centralLineBound_contour_normalization (m h : ℕ) (theta Y : ℝ) :
    ‖((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)‖ *
      (P.n : ℝ) * (P.centralLineBound m h theta Y + P.centralLineBound m h theta Y) =
        P.centralRemainderBound m h theta Y := by
  rw [auxiliaryCommonScale_contour_norm]
  unfold centralLineBound centralRemainderBound
  rw [pow_succ]
  field_simp
  ring

theorem centralRemainderBound_mono_row (hn : 0 < P.n) (m h : ℕ) (hh : h ≤ m)
    (theta Y : ℝ) (hY : 1 / 2 < Y) :
    P.centralRemainderBound m h theta Y ≤ P.centralRemainderBound m m theta Y := by
  have hnR : (1 : ℝ) ≤ P.n := by exact_mod_cast hn
  have hp := pow_le_pow_right₀ hnR (Nat.add_le_add_right hh 1)
  have hA := horizontalMajorantConstant_pos (B := horizontalB Y)
    (show 0 ≤ Y + 1 / 2 by linarith) m
  have hS := auxiliaryCommonScale_cast_pos M P.n
  unfold centralRemainderBound
  gcongr

end ActualIntervals

theorem actualExponentialRemainder_norm_le_central {M : ℕ} (P : ActualIntervals M)
    (h : Fin M) (hM : 0 < M) (hn : 0 < P.n) (theta Y : ℝ) (hY : 1 / 2 < Y)
    (m : ℕ) (hh : h.val ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖actualExponentialRemainder P h (Complex.I * (theta : ℂ))‖ ≤
      P.centralRemainderBound m h.val theta Y := by
  rw [actualExponentialRemainder_eq_horizontal P h hM hn theta Y hY m hh hd,
    norm_mul, norm_mul, Complex.norm_natCast]
  have hB := P.meromorphic_horizontal_integral_bound hn theta Y hY m h.val hh hd
  have hL := P.meromorphic_horizontal_lower_integral_bound hn theta Y hY m h.val hh hd
  calc
    _ ≤ ‖((auxiliaryCommonScale M P.n : ℚ) : ℂ) / (2 * Real.pi * Complex.I)‖ *
        (P.n : ℝ) * (P.centralLineBound m h.val theta Y + P.centralLineBound m h.val theta Y) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hL hB))
        (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg P.n))
    _ = _ := P.centralLineBound_contour_normalization m h.val theta Y

theorem actualAuxiliaryAtI_norm_le_central {M : ℕ} (P : ActualIntervals M)
    (h : Fin M) (hM : 0 < M) (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (m : ℕ) (hh : h.val ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * lambda ^ j.val‖ ≤
      P.centralRemainderBound m m (Real.pi / 2) Y := by
  have hr := actualExponentialRemainder_norm_le_central P h hM hn (Real.pi / 2) Y hY m hh hd
  rw [← lambda_eq_I_mul_pi_div_two] at hr
  have he := hr.trans (P.centralRemainderBound_mono_row hn m h.val hh (Real.pi / 2) Y hY)
  simpa only [actualExponentialRemainder, exp_lambda_eq_I] using he

theorem actualAuxiliaryAtI_norm_le_central_all_rows {M : ℕ} (P : ActualIntervals M)
    (hM : 0 < M) (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (hd : 2 * ((M - 1) + 2) ≤ P.denominator.natDegree) :
    ∀ h : Fin M,
      ‖∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * lambda ^ j.val‖ ≤
        P.centralRemainderBound (M - 1) (M - 1) (Real.pi / 2) Y := by
  intro h
  exact actualAuxiliaryAtI_norm_le_central P h hM hn Y hY (M - 1) (by omega) hd

end OddPiPowers
