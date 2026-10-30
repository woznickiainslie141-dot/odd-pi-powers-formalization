module

public import OddPiPowers.Analysis.CentralLogIntegral
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! Rational-certified numerical bounds for one actual balanced family. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem balanced_log_two_lower : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

theorem balanced_log_two_upper : Real.log 2 ≤ (3 / 4 : ℝ) := by
  have h := Real.log_two_lt_d9
  linarith

theorem balanced_arctan_lower :
    (3 / 4 : ℝ) * (1 / 256) ≤ Real.arctan (1 / 256) := by
  have hcont : Continuous (fun x : ℝ => (1 : ℝ) / (1 + x ^ 2)) := by
    exact continuous_const.div (by fun_prop) (fun x => by positivity)
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume)
    (f := fun _ : ℝ => (3 / 4 : ℝ)) (g := fun x : ℝ => (1 : ℝ) / (1 + x ^ 2))
    (show (0 : ℝ) ≤ 1 / 256 by norm_num)
    (continuous_const.intervalIntegrable 0 (1 / 256))
    (hcont.intervalIntegrable 0 (1 / 256))
    (fun x hx => by
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 / 256 := hx.2
      have hx2 : x ^ 2 ≤ (1 / 256 : ℝ) ^ 2 := by nlinarith
      apply (le_div_iff₀ (show 0 < 1 + x ^ 2 by positivity)).2
      nlinarith)
  norm_num [integral_one_div_one_add_sq] at hmono ⊢
  exact hmono

theorem balanced_log128 : Real.log 128 = 7 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 7
  norm_num at h ⊢
  exact h

theorem balanced_centralIntervalRate_lower :
    Real.log 128 + 3 / 4 ≤ centralIntervalRate 1 128 := by
  have hlog : Real.log (128 ^ 2 : ℝ) ≤ Real.log (128 ^ 2 + 1 / 4 : ℝ) := by
    apply Real.log_le_log (by positivity)
    norm_num
  have hlog2 : Real.log (128 ^ 2 : ℝ) = 2 * Real.log 128 := by
    simpa only [Nat.cast_ofNat] using Real.log_pow (128 : ℝ) 2
  have hatan := balanced_arctan_lower
  unfold centralIntervalRate
  norm_num only [one_pow, Real.log_one, mul_zero, sub_zero] at *
  rw [hlog2] at hlog
  linarith

noncomputable def balancedD0 : ℝ :=
  512 * centralIntervalRate 1 128 - (Real.pi / 2) * 128 - 511

noncomputable def balancedG0 : ℝ := 511 + 512 * Real.log 2

theorem balancedD0_lower : (2000 : ℝ) ≤ balancedD0 := by
  have hf := balanced_centralIntervalRate_lower
  have hl := balanced_log_two_lower
  have hp := Real.pi_le_four
  rw [balanced_log128] at hf
  unfold balancedD0
  linarith

theorem balancedG0_upper : balancedG0 ≤ 900 := by
  have h := balanced_log_two_upper
  unfold balancedG0
  linarith

theorem balanced_numeric_positive_gap : (0 : ℝ) < 2000 - 2 * 900 := by norm_num

theorem balanced_numeric_strict_cross :
    (511 : ℝ) * (2000 + 900) < 7500 * (2000 - 2 * 900) := by norm_num

end OddPiPowers
