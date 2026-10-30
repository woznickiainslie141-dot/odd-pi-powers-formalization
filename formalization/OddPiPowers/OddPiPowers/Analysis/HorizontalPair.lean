module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The real algebra behind the global horizontal-contour tail bound. -/

@[expose] public section

namespace OddPiPowers

theorem pair_ratio_of_coefficient_bounds (D B A v q : ℝ)
    (hD : 0 < D) (hB : 0 < B) (hq : 0 ≤ q)
    (hlin : D ≤ (A - v) * B) (hquad : D ≤ B ^ 2) :
    (1 + q / B) ^ 2 ≤ 1 + (2 * (A - v) * q + q ^ 2) / D := by
  have h1 : 2 / B ≤ 2 * (A - v) / D := by
    apply (div_le_div_iff₀ hB hD).2
    nlinarith [hlin]
  have h2 : 1 / B ^ 2 ≤ 1 / D := by
    exact one_div_le_one_div_of_le hD hquad
  have h1q := mul_le_mul_of_nonneg_right h1 hq
  have h2q := mul_le_mul_of_nonneg_right h2 (sq_nonneg q)
  calc
    (1 + q / B) ^ 2 = 1 + (2 / B) * q + (1 / B ^ 2) * q ^ 2 := by ring
    _ ≤ 1 + (2 * (A - v) / D) * q + (1 / D) * q ^ 2 := by linarith
    _ = 1 + (2 * (A - v) * q + q ^ 2) / D := by ring

theorem paired_horizontal_ratio (A s v q : ℝ) (hs : 0 ≤ s)
    (hAs : s < A) (hv : 0 ≤ v) (hvs : v ≤ s) (hq : 0 ≤ q) :
    let B := (A + s) ^ 2 / (A - s)
    (1 + q / B) ^ 2 ≤ 1 + (2 * (A - v) * q + q ^ 2) / (A + v) ^ 2 := by
  let B := (A + s) ^ 2 / (A - s)
  have hA : 0 < A := lt_of_le_of_lt hs hAs
  have hplus : 0 < A + s := by linarith
  have hAv : 0 < A + v := by linarith
  have hB : 0 < B := div_pos (sq_pos_of_pos hplus) (sub_pos.2 hAs)
  have hsq : (A + v) ^ 2 ≤ (A + s) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hvs) (show 0 ≤ 2 * A + s + v by linarith)]
  have hcancel : (A + s) ^ 2 = B * (A - s) := by
    dsimp [B]
    exact (div_mul_cancel₀ _ (sub_ne_zero.2 hAs.ne')).symm
  have hlin : (A + v) ^ 2 ≤ (A - v) * B := by
    calc
      (A + v) ^ 2 ≤ (A + s) ^ 2 := hsq
      _ = B * (A - s) := hcancel
      _ ≤ B * (A - v) := mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ = (A - v) * B := mul_comm _ _
  have hbase : A + v ≤ B := by
    have hh := mul_le_mul_of_nonneg_right (show A - v ≤ A + v by linarith) hB.le
    nlinarith
  have hquad : (A + v) ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - (A + v))]
  exact pair_ratio_of_coefficient_bounds ((A + v) ^ 2) B A v q
    (sq_pos_of_pos hAv) hB hq hlin hquad

/-- The exact scalar inequality used for the pair of offsets `u,-u`.
Taking finite products and connecting to the complex norm remain separate
tasks; this theorem is uniform in the whole real horizontal coordinate. -/
theorem horizontal_pair_tail (Y u t : ℝ) (hY : 1 / 2 < Y) (hu : |u| ≤ 1 / 2) :
    let B := (Y ^ 2 + 1 / 4) ^ 2 / (Y ^ 2 - 1 / 4)
    (1 + t ^ 2 / B) ^ 2 ≤
      1 + (2 * (Y ^ 2 - u ^ 2) * t ^ 2 + (t ^ 2) ^ 2) / (Y ^ 2 + u ^ 2) ^ 2 := by
  apply paired_horizontal_ratio (Y ^ 2) (1 / 4) (u ^ 2) (t ^ 2)
  · norm_num
  · nlinarith
  · exact sq_nonneg u
  · rcases abs_le.1 hu with ⟨hl, hr⟩
    nlinarith
  · exact sq_nonneg t

theorem normSq_horizontal_factor (x Y : ℝ) :
    Complex.normSq ((x : ℂ) + Complex.I * (Y : ℂ)) = x ^ 2 + Y ^ 2 := by
  simp [Complex.normSq_apply, pow_two]

/-- Exact connection between the scalar ratio and the paired complex
factors in the manuscript. -/
theorem paired_normSq_ratio (Y u t : ℝ) (hY : Y ≠ 0) :
    Complex.normSq ((((t + u : ℝ) : ℂ) + Complex.I * (Y : ℂ)) *
      (((t - u : ℝ) : ℂ) + Complex.I * (Y : ℂ))) /
      Complex.normSq (((u : ℂ) + Complex.I * (Y : ℂ)) *
        (((-u : ℝ) : ℂ) + Complex.I * (Y : ℂ))) =
      1 + (2 * (Y ^ 2 - u ^ 2) * t ^ 2 + (t ^ 2) ^ 2) / (Y ^ 2 + u ^ 2) ^ 2 := by
  simp only [Complex.normSq_mul, normSq_horizontal_factor, neg_sq]
  have hd : Y ^ 2 + u ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_pos_of_ne_zero hY, sq_nonneg u])
  field_simp [hd]
  ring

end OddPiPowers
