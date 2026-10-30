module

public import OddPiPowers.Analysis.BalancedNumericCertificate

/-! A rational cubic lower bound sufficient at the fixed P6 height. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem arctan_cubic_lower (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hcont : Continuous (fun t : ℝ => (1 : ℝ) / (1 + t ^ 2)) := by
    exact continuous_const.div (by fun_prop) (fun t => by positivity)
  have hpoly : Continuous (fun t : ℝ => 1 - t ^ 2) := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => 1 - t ^ 2) (g := fun t : ℝ => (1 : ℝ) / (1 + t ^ 2))
    hx (hpoly.intervalIntegrable 0 x) (hcont.intervalIntegrable 0 x)
    (fun t ht => by
      apply (le_div_iff₀ (show 0 < 1 + t ^ 2 by positivity)).mpr
      nlinarith [sq_nonneg (t ^ 2)])
  have hi : (∫ t : ℝ in 0..x, (1 - t ^ 2)) = x - x ^ 3 / 3 := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 x)
      ((by fun_prop : Continuous (fun t : ℝ => t ^ 2)).intervalIntegrable 0 x)]
    norm_num [integral_pow]
  rw [hi, integral_one_div_one_add_sq] at hmono
  simpa only [Real.arctan_zero, sub_zero] using hmono

end OddPiPowers
