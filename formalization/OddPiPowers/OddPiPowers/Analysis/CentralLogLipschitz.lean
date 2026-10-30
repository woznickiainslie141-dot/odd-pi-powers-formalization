module

public import OddPiPowers.Analysis.CentralLogIntegral
public import OddPiPowers.Analysis.GridIntegralBound

/-! The central logarithm is globally Lipschitz at every positive height. -/

@[expose] public section

namespace OddPiPowers

noncomputable def centralLogIntegrand (Y u : ℝ) : ℝ :=
  Real.log (Real.sqrt (u ^ 2 + Y ^ 2))

theorem centralLogIntegrand_eq (Y u : ℝ) :
    centralLogIntegrand Y u = (1 / 2 : ℝ) * Real.log (u ^ 2 + Y ^ 2) := by
  rw [centralLogIntegrand, Real.log_sqrt (by positivity)]
  ring

theorem centralLogIntegrand_hasDerivAt (Y u : ℝ) (hY : 0 < Y) :
    HasDerivAt (centralLogIntegrand Y) (u / (u ^ 2 + Y ^ 2)) u := by
  have hq : u ^ 2 + Y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have he : centralLogIntegrand Y = fun u => (1 / 2 : ℝ) * Real.log (u ^ 2 + Y ^ 2) :=
    funext (centralLogIntegrand_eq Y)
  rw [he]
  have hp := ((((hasDerivAt_id u).pow 2).add_const (Y ^ 2)).log hq).const_mul (1 / 2)
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hp
  convert hp using 1
  field_simp

theorem centralLogIntegrand_continuous (Y : ℝ) (hY : 0 < Y) :
    Continuous (centralLogIntegrand Y) :=
  continuous_iff_continuousAt.mpr (fun u => (centralLogIntegrand_hasDerivAt Y u hY).continuousAt)

theorem centralLogIntegrand_derivative_bound (Y u : ℝ) (hY : 0 < Y) :
    ‖u / (u ^ 2 + Y ^ 2)‖ ≤ 1 / Y := by
  have hq : 0 < u ^ 2 + Y ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hq, div_le_div_iff₀ hq hY]
  have ht := sq_nonneg (|u| - Y)
  have hu := mul_nonneg (abs_nonneg u) hY.le
  nlinarith [sq_abs u]

theorem centralLogIntegrand_lipschitz (Y : ℝ) (hY : 0 < Y) (x y : ℝ) :
    ‖centralLogIntegrand Y x - centralLogIntegrand Y y‖ ≤ (1 / Y) * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (centralLogIntegrand_hasDerivAt Y u hY).hasDerivWithinAt)
      (fun u hu => centralLogIntegrand_derivative_bound Y u hY)
      (Set.mem_univ y) (Set.mem_univ x)

end OddPiPowers
