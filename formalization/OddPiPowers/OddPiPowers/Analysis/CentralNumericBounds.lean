module

public import OddPiPowers.Analysis.LogRationalBounds
public import OddPiPowers.Analysis.ArctanRationalBounds

/-! A rational lower certificate for each central interval contribution. -/

@[expose] public section

namespace OddPiPowers

def centralRationalLower (c Y a b : ℚ) : ℚ :=
  c / 2 * (13 * (6931471803 / 10000000000) + a) + c * b +
    2 * Y * (c / (2 * Y) - (c / (2 * Y)) ^ 3 / 3)

theorem centralIntervalRate_from_logs (c Y a b : ℚ) (hc : 0 < c) (hY : 0 < Y)
    (ha : (a : ℝ) ≤ Real.log ((((Y ^ 2 + c ^ 2 / 4) / 8192 : ℚ) : ℝ)))
    (hb : (b : ℝ) ≤ Real.log (((1 / c : ℚ) : ℝ))) :
    (centralRationalLower c Y a b : ℝ) ≤ centralIntervalRate (c : ℝ) (Y : ℝ) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hz : (0 : ℝ) < (Y : ℝ) ^ 2 + (c : ℝ) ^ 2 / 4 := by positivity
  have hp : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
    have ht := Real.log_pow (2 : ℝ) 13
    norm_num at ht ⊢
    exact ht
  have ha' : (a : ℝ) ≤ Real.log ((Y : ℝ) ^ 2 + (c : ℝ) ^ 2 / 4) - 13 * Real.log 2 := by
    simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat,
      Real.log_div hz.ne' (by norm_num : (8192 : ℝ) ≠ 0), hp] using ha
  have hb' : (b : ℝ) ≤ -Real.log (c : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, one_div, Rat.cast_inv, Real.log_inv] using hb
  have hl2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    have ht := Real.log_two_gt_d9
    norm_num at ht ⊢
    exact ht.le
  have hfirst : 13 * (6931471803 / 10000000000 : ℝ) + (a : ℝ) ≤
      Real.log ((Y : ℝ) ^ 2 + (c : ℝ) ^ 2 / 4) := by linarith
  have hfirst' := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ (c : ℝ) / 2)
  have hsecond := mul_le_mul_of_nonneg_left hb' hcR.le
  have hatan := arctan_cubic_lower ((c : ℝ) / (2 * (Y : ℝ))) (by positivity)
  have hthird := mul_le_mul_of_nonneg_left hatan (by positivity : 0 ≤ 2 * (Y : ℝ))
  unfold centralRationalLower centralIntervalRate
  push_cast
  nlinarith

end OddPiPowers
