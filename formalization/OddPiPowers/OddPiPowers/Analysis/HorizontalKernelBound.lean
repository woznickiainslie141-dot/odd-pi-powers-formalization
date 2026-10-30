module

public import OddPiPowers.Analysis.ActualHorizontalTail
public import OddPiPowers.Analysis.HorizontalMajorant
public import Mathlib.Topology.Algebra.Polynomial

/-! Bounds for the actual rational kernel, uniformly in the row index. -/

@[expose] public section

namespace OddPiPowers

theorem horizontalPoint_norm_le (n : ℕ) (Y t : ℝ) (hY : 0 ≤ Y) :
    ‖horizontalPoint n Y t‖ ≤ (n : ℝ) * (|t| + Y + 1 / 2) := by
  rw [horizontalPoint, norm_mul, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  calc
    _ ≤ ‖((t - 1 / 2 : ℝ) : ℂ)‖ + ‖Complex.I * (Y : ℂ)‖ := norm_add_le _ _
    _ = |t - 1 / 2| + Y := by
      simp only [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
        Real.norm_eq_abs, abs_of_nonneg hY]
    _ ≤ |t| + Y + 1 / 2 := by
      have h := abs_sub t (1 / 2 : ℝ)
      norm_num at h
      linarith

theorem horizontalPoint_norm_neg_height (n : ℕ) (Y t : ℝ) :
    ‖horizontalPoint n (-Y) t‖ = ‖horizontalPoint n Y t‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [horizontalPoint, Complex.normSq_mul, normSq_horizontal_factor, neg_sq]

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def horizontalKernel (h : ℕ) (Y t : ℝ) : ℂ :=
  horizontalPoint P.n Y t ^ h / P.horizontalDenominator Y t

theorem horizontalKernel_bound (hn : 0 < P.n) (Y t : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.horizontalKernel h Y t‖ ≤
      (P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖ *
        horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  have hn0 : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hq0 : 0 < ‖P.horizontalDenominator Y 0‖ :=
    norm_pos_iff.mpr (P.horizontalDenominator_ne_zero hn Y 0 (by linarith))
  have hqt : 0 < ‖P.horizontalDenominator Y t‖ :=
    norm_pos_iff.mpr (P.horizontalDenominator_ne_zero hn Y t (by linarith))
  have hv : 0 < 1 + t ^ 2 / horizontalB Y := by
    have := horizontalB_pos hY
    positivity
  have hc : 1 ≤ |t| + (Y + 1 / 2) := by linarith [abs_nonneg t]
  have hp := pow_le_pow_left₀ (norm_nonneg _) (horizontalPoint_norm_le P.n Y t (by linarith)) h
  have hpow := pow_le_pow_right₀ hc hh
  have hnum : ‖horizontalPoint P.n Y t‖ ^ h ≤
      (P.n : ℝ) ^ h * (|t| + (Y + 1 / 2)) ^ m := by
    calc
      _ ≤ ((P.n : ℝ) * (|t| + Y + 1 / 2)) ^ h := hp
      _ = (P.n : ℝ) ^ h * (|t| + (Y + 1 / 2)) ^ h := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (pow_nonneg hn0.le _)
  have htail := P.horizontalDenominator_tail_pow hn Y t hY (m + 2) hd
  calc
    ‖P.horizontalKernel h Y t‖ = ‖horizontalPoint P.n Y t‖ ^ h /
        ‖P.horizontalDenominator Y t‖ := by rw [horizontalKernel, norm_div, norm_pow]
    _ ≤ ((P.n : ℝ) ^ h * (|t| + (Y + 1 / 2)) ^ m) /
        ‖P.horizontalDenominator Y t‖ := div_le_div_of_nonneg_right hnum hqt.le
    _ ≤ ((P.n : ℝ) ^ h * (|t| + (Y + 1 / 2)) ^ m) /
        ((1 + t ^ 2 / horizontalB Y) ^ (m + 2) * ‖P.horizontalDenominator Y 0‖) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos (pow_pos hv _) hq0) htail
    _ = _ := by
      simp only [horizontalMajorant, div_eq_mul_inv, mul_inv_rev]
      ring

theorem horizontalKernel_norm_neg_height (hn : 0 < P.n) (h : ℕ) (Y t : ℝ) :
    ‖P.horizontalKernel h (-Y) t‖ = ‖P.horizontalKernel h Y t‖ := by
  simp only [horizontalKernel, norm_div, norm_pow,
    horizontalPoint_norm_neg_height, P.horizontalDenominator_norm_neg_height hn]

theorem horizontalKernel_lower_bound (hn : 0 < P.n) (Y t : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.horizontalKernel h (-Y) t‖ ≤
      (P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖ *
        horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  rw [P.horizontalKernel_norm_neg_height hn]
  exact P.horizontalKernel_bound hn Y t hY m h hh hd

end ActualIntervals
end OddPiPowers
