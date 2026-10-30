module

public import OddPiPowers.Analysis.HorizontalKernelIntegrable
public import OddPiPowers.Analysis.ContourExponential
public import OddPiPowers.Analysis.ActualPartialFractions

/-! Exponential-weighted actual horizontal kernels on both lines. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

open MeasureTheory

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def weightedHorizontalKernel (h : ℕ) (theta Y t : ℝ) : ℂ :=
  contourExponential (Complex.I * (theta : ℂ)) P.n (horizontalPoint P.n Y t) *
    P.horizontalKernel h Y t

theorem weightedHorizontalKernel_bound (hn : 0 < P.n) (theta Y t : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.weightedHorizontalKernel h theta Y t‖ ≤
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)) *
          horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  rw [weightedHorizontalKernel, norm_mul]
  have h := mul_le_mul (contourExponential_norm_horizontal_le theta Y t P.n)
    (P.horizontalKernel_bound hn Y t hY m h hh hd) (norm_nonneg _)
    (Real.exp_pos _).le
  simpa only [mul_assoc] using h

theorem weightedHorizontalKernel_lower_bound (hn : 0 < P.n) (theta Y t : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.weightedHorizontalKernel h theta (-Y) t‖ ≤
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)) *
          horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  rw [weightedHorizontalKernel, norm_mul]
  have h := mul_le_mul (contourExponential_norm_horizontal_neg_le theta Y t P.n)
    (P.horizontalKernel_lower_bound hn Y t hY m h hh hd) (norm_nonneg _)
    (Real.exp_pos _).le
  simpa only [mul_assoc] using h

theorem continuous_weightedHorizontalKernel (hn : 0 < P.n) (h : ℕ)
    (theta Y : ℝ) (hY : Y ≠ 0) : Continuous (P.weightedHorizontalKernel h theta Y) :=
  ((contourExponential_continuous _ P.n).comp (continuous_horizontalPoint P.n Y)).mul
    (P.continuous_horizontalKernel hn h Y hY)

theorem integrable_weightedHorizontalKernel (hn : 0 < P.n) (theta Y : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (P.weightedHorizontalKernel h theta Y) := by
  have hi := (integrable_horizontalMajorant (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m).const_mul
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖))
  apply hi.mono' (P.continuous_weightedHorizontalKernel hn h theta Y (by linarith)).aestronglyMeasurable
  filter_upwards [] with t
  exact P.weightedHorizontalKernel_bound hn theta Y t hY m h hh hd

theorem integrable_weightedHorizontalKernel_lower (hn : 0 < P.n) (theta Y : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    Integrable (P.weightedHorizontalKernel h theta (-Y)) := by
  have hi := (integrable_horizontalMajorant (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m).const_mul
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖))
  apply hi.mono' (P.continuous_weightedHorizontalKernel hn h theta (-Y) (by linarith)).aestronglyMeasurable
  filter_upwards [] with t
  exact P.weightedHorizontalKernel_lower_bound hn theta Y t hY m h hh hd

theorem weightedHorizontalKernel_integral_bound (hn : 0 < P.n) (theta Y : ℝ)
    (hY : 1 / 2 < Y) (m h : ℕ) (hh : h ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖∫ t : ℝ, P.weightedHorizontalKernel h theta Y t‖ ≤
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖)) *
          ∫ t : ℝ, horizontalMajorant (horizontalB Y) (Y + 1 / 2) m t := by
  have hi := P.integrable_weightedHorizontalKernel hn theta Y hY m h hh hd
  have hg := (integrable_horizontalMajorant (horizontalB_pos hY)
    (show 0 ≤ Y + 1 / 2 by linarith) m).const_mul
      (Real.exp (|theta| * ((P.n : ℝ) * |Y|)) *
        ((P.n : ℝ) ^ h / ‖P.horizontalDenominator Y 0‖))
  calc
    _ ≤ ∫ t : ℝ, ‖P.weightedHorizontalKernel h theta Y t‖ := norm_integral_le_integral_norm _
    _ ≤ _ := (integral_mono hi.norm hg
      (fun t => P.weightedHorizontalKernel_bound hn theta Y t hY m h hh hd)).trans_eq
        (integral_const_mul _ _)

end OddPiPowers.ActualIntervals
