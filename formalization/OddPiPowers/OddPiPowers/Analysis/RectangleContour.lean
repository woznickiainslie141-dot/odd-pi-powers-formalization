module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic.Ring

/-! Positively oriented rectangular boundaries and their finite linearity. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

noncomputable def rectangleIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
  (∫ x : ℝ in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I)) +
    Complex.I * (∫ y : ℝ in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I))

structure RectangleIntegrable (f : ℂ → ℂ) (a b c d : ℝ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) volume a b
  top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) volume a b
  right : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume c d
  left : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume c d

theorem rectangleIntegrable_of_continuous {f : ℂ → ℂ} (hf : Continuous f) (a b c d : ℝ) :
    RectangleIntegrable f a b c d := by
  constructor <;> apply Continuous.intervalIntegrable <;> fun_prop

theorem rectangleIntegral_eq_zero_of_differentiable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (a b c d : ℝ) : rectangleIntegral f a b c d = 0 := by
  have ht := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I) hf.differentiableOn
  simpa only [rectangleIntegral, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_mul, zero_sub, zero_add, smul_eq_mul] using ht

theorem rectangleIntegral_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (hg : RectangleIntegrable g a b c d) :
    rectangleIntegral (fun z => f z + g z) a b c d =
      rectangleIntegral f a b c d + rectangleIntegral g a b c d := by
  unfold rectangleIntegral
  rw [intervalIntegral.integral_add hf.bottom hg.bottom,
    intervalIntegral.integral_add hf.top hg.top,
    intervalIntegral.integral_add hf.right hg.right,
    intervalIntegral.integral_add hf.left hg.left]
  ring

theorem rectangleIntegral_const_mul (k : ℂ) (f : ℂ → ℂ) (a b c d : ℝ) :
    rectangleIntegral (fun z => k * f z) a b c d = k * rectangleIntegral f a b c d := by
  simp only [rectangleIntegral, intervalIntegral.integral_const_mul]
  ring

end OddPiPowers
