module

public import OddPiPowers.Analysis.RectangleContour
public import OddPiPowers.Analysis.ActualContourBounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Horizontal truncation limits and affine whole-line change of variables. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory Filter
open scoped Topology

/-- The normalized horizontal parameter `t = x / n + 1/2`. -/
theorem horizontalPoint_affine (n : ℕ) (hn : 0 < n) (Y x : ℝ) :
    horizontalPoint n Y (x / (n : ℝ) + 1 / 2) =
      (x : ℂ) + (((n : ℝ) * Y : ℝ) : ℂ) * Complex.I := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [horizontalPoint, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  field_simp
  ring

/-- Transfer integrability and the whole-line integral through the affine
horizontal parametrization. The Jacobian is `n`, not its reciprocal. -/
theorem horizontal_affine_transfer (f : ℂ → ℂ) (n : ℕ) (hn : 0 < n) (Y : ℝ)
    (hf : Integrable (fun t : ℝ => f (horizontalPoint n Y t))) :
    Integrable (fun x : ℝ => f ((x : ℂ) + (((n : ℝ) * Y : ℝ) : ℂ) * Complex.I)) ∧
    (∫ x : ℝ, f ((x : ℂ) + (((n : ℝ) * Y : ℝ) : ℂ) * Complex.I)) =
      (n : ℂ) * ∫ t : ℝ, f (horizontalPoint n Y t) := by
  let g : ℝ → ℂ := fun t => f (horizontalPoint n Y t)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hshift : Integrable (fun t : ℝ => g (t + 1 / 2)) := hf.comp_add_right (1 / 2)
  have hint := hshift.comp_div hn0
  have hfun : (fun x : ℝ => g (x / (n : ℝ) + 1 / 2)) =
      (fun x : ℝ => f ((x : ℂ) + (((n : ℝ) * Y : ℝ) : ℂ) * Complex.I)) := by
    funext x
    simp only [g, horizontalPoint_affine n hn Y x]
  constructor
  · rw [← hfun]
    exact hint
  · rw [← hfun]
    rw [Measure.integral_comp_div (fun t : ℝ => g (t + 1 / 2)) (n : ℝ)]
    rw [integral_add_right_eq_self g (1 / 2), abs_of_pos hnpos]
    simp [g]

theorem intervalIntegral_symmetric_tendsto {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ x in -R..R, f x) atTop (𝓝 (∫ x, f x)) := by
  exact intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem integrable_kernel_horizontal_real (hn : 0 < P.n)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (fun x : ℝ => P.meromorphicExponentialKernel h
      (Complex.I * (theta : ℂ)) ((x : ℂ) + (((P.n : ℝ) * Y : ℝ) : ℂ) * Complex.I)) :=
  (horizontal_affine_transfer _ P.n hn Y
    (P.integrable_meromorphicExponentialKernel_horizontal hn theta Y hY m h hh hd)).1

theorem integrable_kernel_horizontal_real_lower (hn : 0 < P.n)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (fun x : ℝ => P.meromorphicExponentialKernel h
      (Complex.I * (theta : ℂ)) ((x : ℂ) + ((-((P.n : ℝ) * Y) : ℝ) : ℂ) * Complex.I)) := by
  simpa only [mul_neg] using
    (horizontal_affine_transfer _ P.n hn (-Y)
      (P.integrable_meromorphicExponentialKernel_horizontal_lower hn theta Y hY m h hh hd)).1

theorem kernel_rectangle_tendsto_horizontal (hn : 0 < P.n)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Tendsto (fun R : ℝ => rectangleIntegral
      (P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ)))
      (-R) R (-((P.n : ℝ) * Y)) ((P.n : ℝ) * Y)) atTop
      (𝓝 ((∫ x : ℝ, P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ))
        ((x : ℂ) + ((-((P.n : ℝ) * Y) : ℝ) : ℂ) * Complex.I)) -
       (∫ x : ℝ, P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ))
        ((x : ℂ) + (((P.n : ℝ) * Y : ℝ) : ℂ) * Complex.I)))) := by
  have hYpos : 0 < Y := by linarith
  have hH : 0 ≤ (P.n : ℝ) * Y := by positivity
  have hd' : h + 2 ≤ P.denominator.natDegree := by omega
  have hl := intervalIntegral_symmetric_tendsto
    (P.integrable_kernel_horizontal_real_lower hn theta Y hY m h hh hd)
  have hu := intervalIntegral_symmetric_tendsto
    (P.integrable_kernel_horizontal_real hn theta Y hY m h hh hd)
  have hr := P.meromorphicExponentialKernel_vertical_tendsto_right
    ((P.n : ℝ) * Y) hH theta h hd'
  have hv := P.meromorphicExponentialKernel_vertical_tendsto_left
    ((P.n : ℝ) * Y) hH theta h hd'
  have hlim := (hl.sub hu).add hr |>.sub hv
  simpa [rectangleIntegral, verticalPoint, intervalIntegral.integral_const_mul,
    mul_comm, sub_zero, add_zero] using hlim

theorem kernel_rectangle_tendsto_normalized (hn : 0 < P.n)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Tendsto (fun R : ℝ => rectangleIntegral
      (P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ)))
      (-R) R (-((P.n : ℝ) * Y)) ((P.n : ℝ) * Y)) atTop
      (𝓝 ((P.n : ℂ) *
        ((∫ t : ℝ, P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ))
          (horizontalPoint P.n (-Y) t)) -
         (∫ t : ℝ, P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ))
          (horizontalPoint P.n Y t))))) := by
  have hu := (horizontal_affine_transfer _ P.n hn Y
    (P.integrable_meromorphicExponentialKernel_horizontal hn theta Y hY m h hh hd)).2
  have hl := (horizontal_affine_transfer _ P.n hn (-Y)
    (P.integrable_meromorphicExponentialKernel_horizontal_lower hn theta Y hY m h hh hd)).2
  rw [mul_neg] at hl
  simpa only [hl, hu, ← mul_sub] using
    P.kernel_rectangle_tendsto_horizontal hn theta Y hY m h hh hd

end ActualIntervals
end OddPiPowers
