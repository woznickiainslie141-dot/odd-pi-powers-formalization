module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Elementary central logarithmic integral and its height derivatives.
The helper draft is compiled and integrated by the main process. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

noncomputable def centralLogPrimitive (Y u : ℝ) : ℝ :=
  (u / 2) * Real.log (u ^ 2 + Y ^ 2) - u + Y * Real.arctan (u / Y)

noncomputable def centralIntervalRate (c Y : ℝ) : ℝ :=
  (c / 2) * Real.log (Y ^ 2 + c ^ 2 / 4) - c * Real.log c +
    2 * Y * Real.arctan (c / (2 * Y))

theorem centralLogPrimitive_hasDerivAt (Y u : ℝ) (hY : 0 < Y) :
    HasDerivAt (centralLogPrimitive Y) (Real.log (Real.sqrt (u ^ 2 + Y ^ 2))) u := by
  have hy : Y ≠ 0 := ne_of_gt hY
  have hq : u ^ 2 + Y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have har : 1 + (u / Y) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hp := (((hasDerivAt_id u).div_const 2).mul
      (((hasDerivAt_id u).pow 2 |>.add_const (Y ^ 2)).log hq)).sub
      (hasDerivAt_id u) |>.add
        (((hasDerivAt_id u).div_const Y).arctan.const_mul Y)
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hp
  convert hp using 1
  · rfl
  · rw [Real.log_sqrt (by positivity)]
    field_simp [hy, hq, har]
    ring

theorem centralLogIntegral (c Y : ℝ) (_hc : 0 ≤ c) (hY : 0 < Y) :
    (∫ u : ℝ in -(c / 2)..(c / 2), Real.log (Real.sqrt (u ^ 2 + Y ^ 2))) =
      (c / 2) * Real.log (Y ^ 2 + c ^ 2 / 4) - c +
        2 * Y * Real.arctan (c / (2 * Y)) := by
  have hcont : Continuous (fun u : ℝ => Real.log (Real.sqrt (u ^ 2 + Y ^ 2))) := by
    have hq : Continuous (fun u : ℝ => u ^ 2 + Y ^ 2) := by fun_prop
    exact hq.sqrt.log (fun u => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => centralLogPrimitive_hasDerivAt Y u hY) (hcont.intervalIntegrable _ _)]
  simp only [centralLogPrimitive, neg_sq, neg_div, Real.arctan_neg]
  have harg : (c / 2) / Y = c / (2 * Y) := by
    field_simp [ne_of_gt hY]
  have hsq : (c / 2) ^ 2 + Y ^ 2 = Y ^ 2 + c ^ 2 / 4 := by ring
  rw [hsq, harg]
  ring

theorem centralIntervalRate_eq_integral (c Y : ℝ) (hc : 0 ≤ c) (hY : 0 < Y) :
    centralIntervalRate c Y =
      (∫ u : ℝ in -(c / 2)..(c / 2), Real.log (Real.sqrt (u ^ 2 + Y ^ 2))) +
        c - c * Real.log c := by
  rw [centralLogIntegral c Y hc hY]
  unfold centralIntervalRate
  ring

theorem centralIntervalRate_zero (Y : ℝ) : centralIntervalRate 0 Y = 0 := by
  simp [centralIntervalRate]

theorem centralIntervalRate_hasDerivAt (c Y : ℝ) (hY : 0 < Y) :
    HasDerivAt (centralIntervalRate c) (2 * Real.arctan (c / (2 * Y))) Y := by
  have hy : Y ≠ 0 := ne_of_gt hY
  have hq : Y ^ 2 + c ^ 2 / 4 ≠ 0 := ne_of_gt (by positivity)
  have htwo : (2 * Y : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hy
  have har : 1 + (c / (2 * Y)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hp := ((((hasDerivAt_id Y).pow 2 |>.add_const (c ^ 2 / 4)).log hq).const_mul (c / 2)).sub
      (hasDerivAt_const Y (c * Real.log c)) |>.add
      (((hasDerivAt_id Y).const_mul 2).mul
        (((hasDerivAt_const Y c).div ((hasDerivAt_id Y).const_mul 2) htwo).arctan))
  simp only [Pi.div_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hp
  convert hp using 1
  · rfl
  · field_simp [hy, hq, htwo, har]
    ring

theorem centralIntervalRate_derivative_hasDerivAt (c Y : ℝ) (hY : 0 < Y) :
    HasDerivAt (fun y : ℝ => 2 * Real.arctan (c / (2 * y)))
      (-c / (Y ^ 2 + c ^ 2 / 4)) Y := by
  have hy : Y ≠ 0 := ne_of_gt hY
  have hq : Y ^ 2 + c ^ 2 / 4 ≠ 0 := ne_of_gt (by positivity)
  have htwo : (2 * Y : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hy
  have har : 1 + (c / (2 * Y)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hp := (((hasDerivAt_const Y c).div ((hasDerivAt_id Y).const_mul 2) htwo).arctan).const_mul 2
  simp only [Pi.div_apply, id_eq, mul_one] at hp
  convert hp using 1
  field_simp [hy, hq, htwo, har]
  ring

end OddPiPowers
