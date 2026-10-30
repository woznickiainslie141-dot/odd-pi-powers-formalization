module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! A fixed-degree majorant on the entire real line, with an explicit
integrable Cauchy bound. Constants do not depend on the scale parameter. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

noncomputable def horizontalMajorant (B C : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (|t| + C) ^ m / (1 + t ^ 2 / B) ^ (m + 2)

noncomputable def horizontalMajorantConstant (B C : ℝ) (m : ℕ) : ℝ :=
  (C + 1) ^ m * (max 1 B) ^ (m + 2)

theorem horizontalMajorant_nonneg {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C)
    (m : ℕ) (t : ℝ) : 0 ≤ horizontalMajorant B C m t := by
  unfold horizontalMajorant
  positivity

theorem horizontalMajorant_le_cauchy {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C)
    (m : ℕ) (t : ℝ) :
    horizontalMajorant B C m t ≤
      horizontalMajorantConstant B C m / (1 + t ^ 2) := by
  let u := 1 + t ^ 2
  let v := 1 + t ^ 2 / B
  let H := max 1 B
  have hu : 1 ≤ u := by dsimp [u]; nlinarith [sq_nonneg t]
  have hv : 0 < v := by dsimp [v]; positivity
  have hH : 1 ≤ H := le_max_left _ _
  have hBH : B ≤ H := le_max_right _ _
  have htv : u ≤ H * v := by
    have hq : t ^ 2 ≤ H * (t ^ 2 / B) := by
      have hmul := mul_le_mul_of_nonneg_right hBH (div_nonneg (sq_nonneg t) hB.le)
      have hc : B * (t ^ 2 / B) = t ^ 2 := by field_simp
      rw [hc] at hmul
      exact hmul
    dsimp [u, v]
    nlinarith
  have ht : |t| ≤ u := by
    have hs := sq_nonneg (|t| - 1 / 2)
    dsimp [u]
    nlinarith [sq_abs t]
  have hn : |t| + C ≤ (C + 1) * u := by
    have hh := mul_le_mul_of_nonneg_left hu hC
    nlinarith
  have hn0 : 0 ≤ |t| + C := add_nonneg (abs_nonneg _) hC
  have hp := pow_le_pow_left₀ hn0 hn m
  have hmul := mul_le_mul_of_nonneg_right hp (show 0 ≤ u by linarith)
  have hpower : u ^ (m + 1) ≤ u ^ (m + 2) :=
    pow_le_pow_right₀ hu (by omega)
  have hp2 := pow_le_pow_left₀ (show 0 ≤ u by linarith) htv (m + 2)
  have hA : 0 ≤ (C + 1) ^ m := by positivity
  have hlast : (|t| + C) ^ m * u ≤
      (C + 1) ^ m * H ^ (m + 2) * v ^ (m + 2) := by
    calc
      _ ≤ ((C + 1) * u) ^ m * u := hmul
      _ = (C + 1) ^ m * u ^ (m + 1) := by rw [mul_pow, pow_succ]; ring
      _ ≤ (C + 1) ^ m * u ^ (m + 2) := mul_le_mul_of_nonneg_left hpower hA
      _ ≤ (C + 1) ^ m * (H * v) ^ (m + 2) :=
        mul_le_mul_of_nonneg_left hp2 hA
      _ = _ := by rw [mul_pow]; ring
  exact (div_le_div_iff₀ (pow_pos hv _) (by positivity)).mpr hlast

theorem continuous_horizontalMajorant {B : ℝ} (hB : 0 < B) (C : ℝ) (m : ℕ) :
    Continuous (horizontalMajorant B C m) := by
  unfold horizontalMajorant
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    have : 0 < 1 + t ^ 2 / B := by positivity
    exact pow_ne_zero _ this.ne'

theorem integrable_horizontalMajorant {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C)
    (m : ℕ) : Integrable (horizontalMajorant B C m) := by
  have hi := integrable_inv_one_add_sq.const_mul (horizontalMajorantConstant B C m)
  apply hi.mono' (continuous_horizontalMajorant hB C m).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (horizontalMajorant_nonneg hB hC m t)]
  simpa only [div_eq_mul_inv] using horizontalMajorant_le_cauchy hB hC m t

end OddPiPowers
