module

public import OddPiPowers.Analysis.RectanglePrimitives
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The simple-pole rectangle integral from explicit logarithm primitives.
The left side uses log(-z); its endpoint jumps provide exactly 2*pi*i. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem clog_neg_upper (z : ℂ) (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
  push_cast
  ring

theorem clog_neg_lower (z : ℂ) (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
  push_cast
  ring

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_clog_sub_real (p : ℝ) (z : ℂ) (hz : z - (p : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.log (w - (p : ℂ))) (1 / (z - (p : ℂ))) z := by
  simpa only [Function.comp_def, id_eq, mul_one, one_div] using
    (Complex.hasDerivAt_log hz).comp z ((hasDerivAt_id z).sub_const (p : ℂ))

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_clog_neg_sub_real (p : ℝ) (z : ℂ)
    (hz : -(z - (p : ℂ)) ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.log (-(w - (p : ℂ)))) (1 / (z - (p : ℂ))) z := by
  simpa only [Function.comp_def, id_eq, Pi.neg_apply, one_div, inv_neg,
    neg_mul, mul_neg, mul_one, neg_neg] using
    (Complex.hasDerivAt_log hz).comp z (((hasDerivAt_id z).sub_const (p : ℂ)).neg)

theorem rectangleIntegral_simple_pole (p a b c d : ℝ)
    (ha : a < p) (hb : p < b) (hc : c < 0) (hd : 0 < d) :
    rectangleIntegral (fun z : ℂ => 1 / (z - (p : ℂ))) a b c d =
      2 * Real.pi * Complex.I := by
  let F : ℂ → ℂ := fun z => Complex.log (z - (p : ℂ))
  let G : ℂ → ℂ := fun z => Complex.log (-(z - (p : ℂ)))
  have hi := rectangleIntegrable_pole (fun _ : ℂ => 1) continuous_const p a b c d
    ha.ne hb.ne' hc.ne hd.ne' 1
  simp only [pow_one] at hi
  have hbot : ∀ x : ℝ, HasDerivAt F (1 / ((x : ℂ) + (c : ℂ) * Complex.I - (p : ℂ)))
      ((x : ℂ) + (c : ℂ) * Complex.I) := by
    intro x
    apply hasDerivAt_clog_sub_real
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using hc.ne
  have htop : ∀ x : ℝ, HasDerivAt F (1 / ((x : ℂ) + (d : ℂ) * Complex.I - (p : ℂ)))
      ((x : ℂ) + (d : ℂ) * Complex.I) := by
    intro x
    apply hasDerivAt_clog_sub_real
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using hd.ne'
  have hright : ∀ y : ℝ, HasDerivAt F (1 / ((b : ℂ) + (y : ℂ) * Complex.I - (p : ℂ)))
      ((b : ℂ) + (y : ℂ) * Complex.I) := by
    intro y
    apply hasDerivAt_clog_sub_real
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using sub_pos.mpr hb
  have hleft : ∀ y : ℝ, HasDerivAt G (1 / ((a : ℂ) + (y : ℂ) * Complex.I - (p : ℂ)))
      ((a : ℂ) + (y : ℂ) * Complex.I) := by
    intro y
    apply hasDerivAt_clog_neg_sub_real
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using sub_pos.mpr ha
  have hib := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => horizontal_comp_hasDerivAt x c (hbot x)) hi.bottom
  have hit := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => horizontal_comp_hasDerivAt x d (htop x)) hi.top
  have hir := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => vertical_comp_hasDerivAt b y (hright y)) (hi.right.const_mul Complex.I)
  have hil := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => vertical_comp_hasDerivAt a y (hleft y)) (hi.left.const_mul Complex.I)
  rw [intervalIntegral.integral_const_mul] at hir hil
  unfold rectangleIntegral
  rw [hib, hit, hir, hil]
  dsimp [F, G]
  rw [clog_neg_upper _ (by simpa using hd), clog_neg_lower _ (by simpa using hc)]
  ring

end OddPiPowers
