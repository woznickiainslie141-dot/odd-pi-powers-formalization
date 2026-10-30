module

public import OddPiPowers.Analysis.ActualHorizontalGeometry
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exponential factor for the fixed-index contour representation.

The helper draft was checked by the main chat under the bounded runner. -/

@[expose] public section

namespace OddPiPowers

noncomputable def contourExponential (lambda : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (lambda * (z + n))

theorem contourExponential_norm_imaginary (theta : ℝ) (n : ℕ) (z : ℂ) :
    ‖contourExponential (Complex.I * (theta : ℂ)) n z‖ =
      Real.exp (-theta * z.im) := by
  simp [contourExponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem contourExponential_norm_le_strip (theta H : ℝ) (n : ℕ) (z : ℂ)
    (_hH : 0 ≤ H) (hz : |z.im| ≤ H) :
    ‖contourExponential (Complex.I * (theta : ℂ)) n z‖ ≤
      Real.exp (|theta| * H) := by
  rw [contourExponential_norm_imaginary]
  apply Real.exp_le_exp.mpr
  calc
    -theta * z.im = -(theta * z.im) := by ring
    _ ≤ |theta * z.im| := neg_le_abs _
    _ = |theta| * |z.im| := abs_mul _ _
    _ ≤ |theta| * H := mul_le_mul_of_nonneg_left hz (abs_nonneg _)

theorem horizontalPoint_im (n : ℕ) (Y t : ℝ) :
    (horizontalPoint n Y t).im = (n : ℝ) * Y := by
  simp [horizontalPoint, Complex.mul_im]

theorem contourExponential_norm_horizontal (theta Y t : ℝ) (n : ℕ) :
    ‖contourExponential (Complex.I * (theta : ℂ)) n (horizontalPoint n Y t)‖ =
      Real.exp (-theta * ((n : ℝ) * Y)) := by
  rw [contourExponential_norm_imaginary, horizontalPoint_im]

theorem contourExponential_norm_horizontal_neg (theta Y t : ℝ) (n : ℕ) :
    ‖contourExponential (Complex.I * (theta : ℂ)) n (horizontalPoint n (-Y) t)‖ =
      Real.exp (theta * ((n : ℝ) * Y)) := by
  rw [contourExponential_norm_horizontal]
  congr 1
  ring

/-- The same bound applies to either horizontal line, uniformly in `t`. -/
theorem contourExponential_norm_horizontal_le (theta Y t : ℝ) (n : ℕ) :
    ‖contourExponential (Complex.I * (theta : ℂ)) n (horizontalPoint n Y t)‖ ≤
      Real.exp (|theta| * ((n : ℝ) * |Y|)) := by
  apply contourExponential_norm_le_strip theta ((n : ℝ) * |Y|) n
  · exact mul_nonneg (Nat.cast_nonneg n) (abs_nonneg Y)
  · rw [horizontalPoint_im, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]

theorem contourExponential_norm_horizontal_neg_le (theta Y t : ℝ) (n : ℕ) :
    ‖contourExponential (Complex.I * (theta : ℂ)) n (horizontalPoint n (-Y) t)‖ ≤
      Real.exp (|theta| * ((n : ℝ) * |Y|)) := by
  simpa only [abs_neg] using contourExponential_norm_horizontal_le theta (-Y) t n

theorem contourExponential_factor (lambda : ℂ) (n : ℕ) (z : ℂ) :
    contourExponential lambda n z =
      Complex.exp (lambda * n) * Complex.exp (lambda * z) := by
  rw [contourExponential, ← Complex.exp_add]
  congr 1
  ring

theorem contourExponential_differentiable (lambda : ℂ) (n : ℕ) :
    Differentiable ℂ (contourExponential lambda n) := by
  unfold contourExponential
  exact ((differentiable_id.add_const (n : ℂ)).const_mul lambda).cexp

theorem contourExponential_continuous (lambda : ℂ) (n : ℕ) :
    Continuous (contourExponential lambda n) :=
  (contourExponential_differentiable lambda n).continuous

theorem iteratedDeriv_contourExponential (lambda : ℂ) (n r : ℕ) (z : ℂ) :
    iteratedDeriv r (contourExponential lambda n) z =
      lambda ^ r * contourExponential lambda n z := by
  have hfun : contourExponential lambda n =
      fun w : ℂ => Complex.exp (lambda * n) * Complex.exp (lambda * w) := by
    funext w
    exact contourExponential_factor lambda n w
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
  ring

end OddPiPowers
