module

public import OddPiPowers.Analysis.CentralNumericBounds

/-! Exact rational candidates, certified by finite-series inequalities. -/

@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem p6CentralInterval09_lower : ((5508752669 / 1250000000) : ℝ) ≤
    centralIntervalRate (17 / 23) (2113 / 20) := by
  have haQ : ((154681188437 / 500000000000) : ℚ) ≤ logSeries (2361891701 / 1733427200) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((4723138623 / 15625000000) : ℚ) ≤ logSeries (23 / 17) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (2361891701 / 1733427200) (by norm_num) 10).1
  have hb := (logSeries_bounds (23 / 17) (by norm_num) 10).1
  have haQR : (((154681188437 / 500000000000) : ℚ) : ℝ) ≤ (logSeries (2361891701 / 1733427200) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((4723138623 / 15625000000) : ℚ) : ℝ) ≤ (logSeries (23 / 17) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (17 / 23) (2113 / 20) (154681188437 / 500000000000) (4723138623 / 15625000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((5508752669 / 1250000000) : ℚ) ≤ centralRationalLower (17 / 23) (2113 / 20) (154681188437 / 500000000000) (4723138623 / 15625000000) := by
    norm_num [centralRationalLower]
  have hqR : (((5508752669 / 1250000000) : ℚ) : ℝ) ≤ (centralRationalLower (17 / 23) (2113 / 20) (154681188437 / 500000000000) (4723138623 / 15625000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers
