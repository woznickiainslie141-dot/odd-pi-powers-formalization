module

public import OddPiPowers.Analysis.HorizontalKernelBound

/-! Whole-line integrability and scale-independent normalized domination. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem continuous_horizontalPoint (n : ℕ) (Y : ℝ) :
    Continuous (horizontalPoint n Y) := by
  unfold horizontalPoint
  fun_prop

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem continuous_horizontalDenominator (Y : ℝ) :
    Continuous (P.horizontalDenominator Y) := by
  exact (P.denominator.continuous_eval₂ (Rat.castHom ℂ)).comp
    (continuous_horizontalPoint P.n Y)

theorem continuous_horizontalKernel (hn : 0 < P.n) (h : ℕ) (Y : ℝ) (hY : Y ≠ 0) :
    Continuous (P.horizontalKernel h Y) := by
  exact ((continuous_horizontalPoint P.n Y).pow h).div
    (P.continuous_horizontalDenominator Y) (fun t => P.horizontalDenominator_ne_zero hn Y t hY)

theorem integrable_horizontalKernel (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (P.horizontalKernel h Y) := by
  have hi := (integrable_horizontalMajorant (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m).const_mul
      ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)
  apply hi.mono' (P.continuous_horizontalKernel hn h Y (by linarith)).aestronglyMeasurable
  filter_upwards [] with t
  exact P.horizontalKernel_bound hn Y t hY m h hh hd

theorem integrable_horizontalKernel_lower (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (P.horizontalKernel h (-Y)) := by
  have hi := (integrable_horizontalMajorant (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m).const_mul
      ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)
  apply hi.mono' (P.continuous_horizontalKernel hn h (-Y) (by linarith)).aestronglyMeasurable
  filter_upwards [] with t
  exact P.horizontalKernel_lower_bound hn Y t hY m h hh hd

noncomputable def normalizedHorizontalKernel (h : ℕ) (Y t : ℝ) : ℂ :=
  (P.horizontalDenominator Y 0 / (P.n : ℂ) ^ h) * P.horizontalKernel h Y t

/-- A single dominating function for every row h<=m and every scale whose
degree is large enough. No limit or numerical asymptotic is assumed. -/
theorem normalizedHorizontalKernel_bound (hn : 0 < P.n) (Y t : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.normalizedHorizontalKernel h Y t‖ ≤
      horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  have hq : ‖P.horizontalDenominator Y 0‖ ≠ 0 :=
    (norm_pos_iff.mpr (P.horizontalDenominator_ne_zero hn Y 0 (by linarith))).ne'
  have hn0 : (P.n : ℝ) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  rw [normalizedHorizontalKernel, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (‖P.horizontalDenominator Y 0‖ / (P.n : ℝ) ^ h) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖ *
          horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t) :=
      mul_le_mul_of_nonneg_left (P.horizontalKernel_bound hn Y t hY m h hh hd) (by positivity)
    _ = _ := by field_simp

theorem normalizedHorizontalKernel_lower_bound (hn : 0 < P.n) (Y t : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.normalizedHorizontalKernel h (-Y) t‖ ≤
      horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  simpa only [normalizedHorizontalKernel, norm_mul, norm_div, norm_pow,
    Complex.norm_natCast, P.horizontalDenominator_norm_neg_height hn,
    P.horizontalKernel_norm_neg_height hn] using
    P.normalizedHorizontalKernel_bound hn Y t hY m h hh hd

theorem integrable_normalizedHorizontalKernel (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (P.normalizedHorizontalKernel h Y) :=
  (P.integrable_horizontalKernel hn Y hY m h hh hd).const_mul _

theorem horizontalKernel_integral_bound (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y)
    (m h : ℕ) (hh : h ≤ m) (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖∫ t : ℝ, P.horizontalKernel h Y t‖ ≤
      (P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖ *
        ∫ t : ℝ, horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  have hi := P.integrable_horizontalKernel hn Y hY m h hh hd
  have hg := (integrable_horizontalMajorant (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m).const_mul
      ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)
  calc
    _ ≤ ∫ t : ℝ, ‖P.horizontalKernel h Y t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖ *
        horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t :=
      integral_mono hi.norm hg (fun t => P.horizontalKernel_bound hn Y t hY m h hh hd)
    _ = _ := integral_const_mul _ _

/-- Outer zero-left intervals force the actual denominator degree to grow. -/
theorem denominator_natDegree_ge_n_add_one (a : Fin M) (ha : P.left a = 0) :
    P.n + 1 ≤ P.denominator.natDegree := by
  rw [P.denominator_natDegree, P.totalMultiplicity_eq_sum_interval_card]
  have h := Finset.single_le_sum (f := fun a : Fin M => (P.interval a).card)
    (fun b hb => Nat.zero_le _) (Finset.mem_univ a)
  simpa only [P.interval_card_eq_length_add_one, length, ha, mul_zero, Nat.sub_zero] using h

end ActualIntervals
end OddPiPowers
