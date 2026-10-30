module

public import OddPiPowers.Analysis.HorizontalMajorant

/-! An explicit whole-line constant, independent of scale and row. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem horizontalMajorantConstant_pos {B C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    0 < horizontalMajorantConstant B C m := by
  unfold horizontalMajorantConstant
  have hB : 0 < max 1 B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem horizontalMajorant_integral_nonneg {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C)
    (m : ℕ) : 0 ≤ ∫ t : ℝ, horizontalMajorant B C m t := by
  exact integral_nonneg (horizontalMajorant_nonneg hB hC m)

theorem horizontalMajorant_integral_le {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C)
    (m : ℕ) :
    (∫ t : ℝ, horizontalMajorant B C m t) ≤
      Real.pi * horizontalMajorantConstant B C m := by
  have hg := integrable_horizontalMajorant hB hC m
  have hi := integrable_inv_one_add_sq.const_mul (horizontalMajorantConstant B C m)
  calc
    _ ≤ ∫ t : ℝ, horizontalMajorantConstant B C m * (1 + t ^ 2)⁻¹ :=
      integral_mono hg hi (fun t => by
        simpa only [div_eq_mul_inv] using horizontalMajorant_le_cauchy hB hC m t)
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring

end OddPiPowers
