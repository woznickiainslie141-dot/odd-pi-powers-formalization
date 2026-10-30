module

public import OddPiPowers.Analysis.VerticalKernelBound
public import OddPiPowers.Analysis.ContourExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Fixed-scale vanishing of actual exponential rational vertical sides. -/

@[expose] public section

namespace OddPiPowers

open Filter MeasureTheory
open scoped Topology

noncomputable def verticalPoint (x y : ℝ) : ℂ := (x : ℂ) + Complex.I * (y : ℂ)

theorem continuous_verticalPoint (x : ℝ) : Continuous (verticalPoint x) := by
  unfold verticalPoint
  fun_prop

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def verticalExponentialKernel (h : ℕ) (theta : ℝ) (z : ℂ) : ℂ :=
  contourExponential (Complex.I * (theta : ℂ)) P.n z * (z ^ h / P.denominatorValue z)

noncomputable def verticalTailConstant (h : ℕ) (theta H : ℝ) : ℝ :=
  Real.exp (|theta| * H) * ((2 : ℝ) ^ h * 2 ^ (h + 2))

theorem verticalExponentialKernel_bound (R H : ℝ) (hR : 2 ≤ R)
    (hn : 2 * (P.n : ℝ) ≤ R) (hH : 0 ≤ H) (hHR : H ≤ R)
    (z : ℂ) (hre : |z.re| = R) (him : |z.im| ≤ H)
    (theta : ℝ) (h : ℕ) (hd : h + 2 ≤ P.denominator.natDegree) :
    ‖P.verticalExponentialKernel h theta z‖ ≤ verticalTailConstant h theta H / R ^ 2 := by
  rw [verticalExponentialKernel, norm_mul]
  have hm := mul_le_mul (contourExponential_norm_le_strip theta H P.n z hH him)
    (P.vertical_rationalKernel_bound R hR hn z hre (him.trans hHR) h hd)
    (norm_nonneg _) (Real.exp_pos _).le
  simpa only [verticalTailConstant, mul_div_assoc] using hm

theorem continuous_verticalExponentialKernel (R : ℝ) (hR : 2 ≤ R)
    (hn : 2 * (P.n : ℝ) ≤ R) (x : ℝ) (hx : |x| = R) (theta : ℝ) (h : ℕ) :
    Continuous (fun y : ℝ => P.verticalExponentialKernel h theta (verticalPoint x y)) := by
  have hden : ∀ y : ℝ, P.denominatorValue (verticalPoint x y) ≠ 0 := by
    intro y
    have hre : |(verticalPoint x y).re| = R := by simpa [verticalPoint] using hx
    have hlow := P.vertical_denominator_lower R (by linarith) hn (verticalPoint x y) hre
    exact norm_ne_zero_iff.mp (ne_of_gt ((pow_pos (by linarith : 0 < R / 2) _).trans_le hlow))
  exact ((contourExponential_continuous _ P.n).comp (continuous_verticalPoint x)).mul
    (((continuous_verticalPoint x).pow h).div
      (P.continuous_denominatorValue.comp (continuous_verticalPoint x)) hden)

noncomputable def verticalSideIntegral (h : ℕ) (theta x H : ℝ) : ℂ :=
  ∫ y : ℝ in -H..H, Complex.I * P.verticalExponentialKernel h theta (verticalPoint x y)

theorem verticalSide_intervalIntegrable (R : ℝ) (hR : 2 ≤ R)
    (hn : 2 * (P.n : ℝ) ≤ R) (x : ℝ) (hx : |x| = R) (theta H : ℝ) (h : ℕ) :
    IntervalIntegrable
      (fun y : ℝ => Complex.I * P.verticalExponentialKernel h theta (verticalPoint x y))
      volume (-H) H :=
  (continuous_const.mul (P.continuous_verticalExponentialKernel R hR hn x hx theta h)).intervalIntegrable _ _

theorem verticalSideIntegral_bound (R H : ℝ) (hR : 2 ≤ R)
    (hn : 2 * (P.n : ℝ) ≤ R) (hH : 0 ≤ H) (hHR : H ≤ R)
    (x : ℝ) (hx : |x| = R) (theta : ℝ) (h : ℕ)
    (hd : h + 2 ≤ P.denominator.natDegree) :
    ‖P.verticalSideIntegral h theta x H‖ ≤
      (2 * H * verticalTailConstant h theta H) / R ^ 2 := by
  have hb : ∀ y ∈ Set.uIoc (-H) H,
      ‖Complex.I * P.verticalExponentialKernel h theta (verticalPoint x y)‖ ≤
        verticalTailConstant h theta H / R ^ 2 := by
    intro y hy
    have hy' : -H ≤ y ∧ y ≤ H := by
      have hle : -H ≤ H := by linarith
      rw [Set.uIoc_of_le hle] at hy
      exact ⟨hy.1.le, hy.2⟩
    rw [norm_mul, Complex.norm_I, one_mul]
    apply P.verticalExponentialKernel_bound R H hR hn hH hHR
      (verticalPoint x y) _ _ theta h hd
    · simpa [verticalPoint] using hx
    · simpa [verticalPoint] using abs_le.mpr hy'
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  change ‖P.verticalSideIntegral h theta x H‖ ≤ _ at hi
  have he : |H - -H| = 2 * H := by rw [abs_of_nonneg (by linarith)]; ring
  rw [he] at hi
  convert hi using 1; ring

theorem verticalSideIntegral_tendsto_right (H : ℝ) (hH : 0 ≤ H) (theta : ℝ)
    (h : ℕ) (hd : h + 2 ≤ P.denominator.natDegree) :
    Tendsto (fun R : ℝ => P.verticalSideIntegral h theta R H) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun R : ℝ => (2 * H * verticalTailConstant h theta H) / R ^ 2)
      atTop (𝓝 0) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, div_eq_mul_inv, inv_pow] using
      hi.const_mul (2 * H * verticalTailConstant h theta H)
  apply squeeze_zero' (Eventually.of_forall (fun R => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2 * (P.n : ℝ)),
    eventually_ge_atTop H] with R hR hn hHR
  exact P.verticalSideIntegral_bound R H hR hn hH hHR R (abs_of_nonneg (by linarith)) theta h hd

theorem verticalSideIntegral_tendsto_left (H : ℝ) (hH : 0 ≤ H) (theta : ℝ)
    (h : ℕ) (hd : h + 2 ≤ P.denominator.natDegree) :
    Tendsto (fun R : ℝ => P.verticalSideIntegral h theta (-R) H) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun R : ℝ => (2 * H * verticalTailConstant h theta H) / R ^ 2)
      atTop (𝓝 0) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, div_eq_mul_inv, inv_pow] using
      hi.const_mul (2 * H * verticalTailConstant h theta H)
  apply squeeze_zero' (Eventually.of_forall (fun R => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2 * (P.n : ℝ)),
    eventually_ge_atTop H] with R hR hn hHR
  exact P.verticalSideIntegral_bound R H hR hn hH hHR (-R)
    (by rw [abs_neg, abs_of_nonneg (by linarith)]) theta h hd

end ActualIntervals
end OddPiPowers
