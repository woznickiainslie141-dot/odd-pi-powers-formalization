module

public import OddPiPowers.Analysis.RectangleContour
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp

/-! Boundary primitives and nonvanishing for real poles in rectangles. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

set_option backward.isDefEq.respectTransparency false in
theorem horizontal_comp_hasDerivAt {F : ℂ → ℂ} {v : ℂ} (x y : ℝ)
    (hF : HasDerivAt F v ((x : ℂ) + (y : ℂ) * Complex.I)) :
    HasDerivAt (fun t : ℝ => F ((t : ℂ) + (y : ℂ) * Complex.I)) v x := by
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hF.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * Complex.I))).comp_ofReal

set_option backward.isDefEq.respectTransparency false in
theorem vertical_comp_hasDerivAt {F : ℂ → ℂ} {v : ℂ} (x y : ℝ)
    (hF : HasDerivAt F v ((x : ℂ) + (y : ℂ) * Complex.I)) :
    HasDerivAt (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I)) (Complex.I * v) y := by
  simpa only [Function.comp_def, id_eq, one_mul, mul_one, mul_comm] using
    (hF.comp (y : ℂ) (((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (x : ℂ))).comp_ofReal

theorem rectangleIntegral_eq_zero_of_boundary_primitive (F f : ℂ → ℂ) (a b c d : ℝ)
    (hf : RectangleIntegrable f a b c d)
    (hbot : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f ((x : ℂ) + (c : ℂ) * Complex.I))
      ((x : ℂ) + (c : ℂ) * Complex.I))
    (htop : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f ((x : ℂ) + (d : ℂ) * Complex.I))
      ((x : ℂ) + (d : ℂ) * Complex.I))
    (hri : ∀ y ∈ Set.uIcc c d, HasDerivAt F (f ((b : ℂ) + (y : ℂ) * Complex.I))
      ((b : ℂ) + (y : ℂ) * Complex.I))
    (hle : ∀ y ∈ Set.uIcc c d, HasDerivAt F (f ((a : ℂ) + (y : ℂ) * Complex.I))
      ((a : ℂ) + (y : ℂ) * Complex.I)) : rectangleIntegral f a b c d = 0 := by
  have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => horizontal_comp_hasDerivAt x c (hbot x hx)) hf.bottom
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => horizontal_comp_hasDerivAt x d (htop x hx)) hf.top
  have hr := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => vertical_comp_hasDerivAt b y (hri y hy)) (hf.right.const_mul Complex.I)
  have hl := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => vertical_comp_hasDerivAt a y (hle y hy)) (hf.left.const_mul Complex.I)
  rw [intervalIntegral.integral_const_mul] at hr hl
  unfold rectangleIntegral
  rw [hb, ht, hr, hl]
  ring

theorem rectangle_horizontal_ne_pole (p y x : ℝ) (hy : y ≠ 0) :
    (x : ℂ) + (y : ℂ) * Complex.I - (p : ℂ) ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  apply hy
  simpa using hi

theorem rectangle_vertical_ne_pole (p x y : ℝ) (hx : x ≠ p) :
    (x : ℂ) + (y : ℂ) * Complex.I - (p : ℂ) ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  apply hx
  have hh : x - p = 0 := by simpa using hr
  linarith

theorem rectangleIntegrable_pole (f : ℂ → ℂ) (hf : Continuous f)
    (p a b c d : ℝ) (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ 0) (hd : d ≠ 0) (k : ℕ) :
    RectangleIntegrable (fun z => f z / (z - (p : ℂ)) ^ k) a b c d := by
  constructor
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact pow_ne_zero _ (rectangle_horizontal_ne_pole p c x hc)
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact pow_ne_zero _ (rectangle_horizontal_ne_pole p d x hd)
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro y
    exact pow_ne_zero _ (rectangle_vertical_ne_pole p b y hb)
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro y
    exact pow_ne_zero _ (rectangle_vertical_ne_pole p a y ha)

end OddPiPowers
