module

public import OddPiPowers.Analysis.CentralNumericBounds

/-! Exact rational candidates, certified by finite-series inequalities. -/

@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem p6CentralInterval06_lower : ((48335913479 / 10000000000) : ℝ) ≤
    centralIntervalRate (19 / 23) (2113 / 20) := by
  have haQ : ((309365425273 / 1000000000000) : ℚ) ≤ logSeries (2361898901 / 1733427200) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((95527618381 / 500000000000) : ℚ) ≤ logSeries (23 / 19) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (2361898901 / 1733427200) (by norm_num) 10).1
  have hb := (logSeries_bounds (23 / 19) (by norm_num) 10).1
  have haQR : (((309365425273 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (2361898901 / 1733427200) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((95527618381 / 500000000000) : ℚ) : ℝ) ≤ (logSeries (23 / 19) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (19 / 23) (2113 / 20) (309365425273 / 1000000000000) (95527618381 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((48335913479 / 10000000000) : ℚ) ≤ centralRationalLower (19 / 23) (2113 / 20) (309365425273 / 1000000000000) (95527618381 / 500000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((48335913479 / 10000000000) : ℚ) : ℝ) ≤ (centralRationalLower (19 / 23) (2113 / 20) (309365425273 / 1000000000000) (95527618381 / 500000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers
