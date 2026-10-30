module

public import OddPiPowers.Analysis.ActualContourRemainder
public import OddPiPowers.Analysis.WeightedHorizontal
public import OddPiPowers.Analysis.VerticalSideTail

/-! All contour-side estimates applied to the full actual factorial kernel.
This does not assert a deformation identity between different contours. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

open MeasureTheory Filter
open scoped Topology

variable {M : ℕ} (P : ActualIntervals M)

set_option backward.isDefEq.respectTransparency false in
theorem meromorphicExponentialKernel_circleIntegrable (h : ℕ) (lambda : ℂ) (pole : ℕ) :
    CircleIntegrable (P.meromorphicExponentialKernel h lambda) (-(pole : ℂ)) (1 / 4) := by
  have hn : Continuous (fun z : ℂ => P.intervalFactorialProduct * z ^ h) := by fun_prop
  have hden : ContinuousOn P.denominatorValue (Metric.sphere (-(pole : ℂ)) (1 / 4)) :=
    P.continuous_denominatorValue.continuousOn
  have hc := (hn.continuousOn.div hden (fun z hz =>
    P.denominatorValue_ne_zero_of_nonpoles z
      (fun r hr => all_pole_factors_ne_zero_on_sphere pole r hz))).mul
    (contourExponential_continuous lambda P.n).continuousOn
  exact hc.circleIntegrable (by norm_num)

theorem meromorphicExponentialKernel_horizontal (h : ℕ) (theta Y t : ℝ) :
    P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ)) (horizontalPoint P.n Y t) =
      P.intervalFactorialProduct * P.weightedHorizontalKernel h theta Y t := by
  unfold meromorphicExponentialKernel factorialRationalKernel weightedHorizontalKernel
    horizontalKernel denominatorValue horizontalDenominator
  ring

theorem meromorphicExponentialKernel_vertical (h : ℕ) (theta : ℝ) (z : ℂ) :
    P.meromorphicExponentialKernel h (Complex.I * (theta : ℂ)) z =
      P.intervalFactorialProduct * P.verticalExponentialKernel h theta z := by
  unfold meromorphicExponentialKernel factorialRationalKernel verticalExponentialKernel
  ring

theorem integrable_meromorphicExponentialKernel_horizontal (hn : 0 < P.n)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (fun t : ℝ => P.meromorphicExponentialKernel h
      (Complex.I * (theta : ℂ)) (horizontalPoint P.n Y t)) := by
  simp_rw [P.meromorphicExponentialKernel_horizontal]
  exact (P.integrable_weightedHorizontalKernel hn theta Y hY m h hh hd).const_mul _

theorem integrable_meromorphicExponentialKernel_horizontal_lower (hn : 0 < P.n)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (fun t : ℝ => P.meromorphicExponentialKernel h
      (Complex.I * (theta : ℂ)) (horizontalPoint P.n (-Y) t)) := by
  simp_rw [P.meromorphicExponentialKernel_horizontal]
  exact (P.integrable_weightedHorizontalKernel_lower hn theta Y hY m h hh hd).const_mul _

theorem meromorphicExponentialKernel_vertical_integral (h : ℕ) (theta x H : ℝ) :
    (∫ y : ℝ in -H..H, Complex.I * P.meromorphicExponentialKernel h
      (Complex.I * (theta : ℂ)) (verticalPoint x y)) =
        P.intervalFactorialProduct * P.verticalSideIntegral h theta x H := by
  unfold verticalSideIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only
  rw [P.meromorphicExponentialKernel_vertical]
  ring

theorem meromorphicExponentialKernel_vertical_tendsto_right
    (H : ℝ) (hH : 0 ≤ H) (theta : ℝ) (h : ℕ)
    (hd : h + 2 ≤ P.denominator.natDegree) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in -H..H, Complex.I * P.meromorphicExponentialKernel h
      (Complex.I * (theta : ℂ)) (verticalPoint R y)) atTop (𝓝 0) := by
  simp_rw [P.meromorphicExponentialKernel_vertical_integral]
  simpa only [mul_zero] using
    (P.verticalSideIntegral_tendsto_right H hH theta h hd).const_mul P.intervalFactorialProduct

theorem meromorphicExponentialKernel_vertical_tendsto_left
    (H : ℝ) (hH : 0 ≤ H) (theta : ℝ) (h : ℕ)
    (hd : h + 2 ≤ P.denominator.natDegree) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in -H..H, Complex.I * P.meromorphicExponentialKernel h
      (Complex.I * (theta : ℂ)) (verticalPoint (-R) y)) atTop (𝓝 0) := by
  simp_rw [P.meromorphicExponentialKernel_vertical_integral]
  simpa only [mul_zero] using
    (P.verticalSideIntegral_tendsto_left H hH theta h hd).const_mul P.intervalFactorialProduct

end OddPiPowers.ActualIntervals
