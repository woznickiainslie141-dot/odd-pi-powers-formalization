module

public import OddPiPowers.Analysis.CentralNumericBounds

/-! Exact rational candidates, certified by finite-series inequalities. -/

@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem p6CentralInterval03_lower : ((10502020807 / 2000000000) : ℝ) ≤
    centralIntervalRate (21 / 23) (2113 / 20) := by
  have haQ : ((309368812373 / 1000000000000) : ℚ) ≤ logSeries (2361906901 / 1733427200) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((18194355641 / 200000000000) : ℚ) ≤ logSeries (23 / 21) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (2361906901 / 1733427200) (by norm_num) 10).1
  have hb := (logSeries_bounds (23 / 21) (by norm_num) 10).1
  have haQR : (((309368812373 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (2361906901 / 1733427200) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((18194355641 / 200000000000) : ℚ) : ℝ) ≤ (logSeries (23 / 21) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (21 / 23) (2113 / 20) (309368812373 / 1000000000000) (18194355641 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((10502020807 / 2000000000) : ℚ) ≤ centralRationalLower (21 / 23) (2113 / 20) (309368812373 / 1000000000000) (18194355641 / 200000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((10502020807 / 2000000000) : ℚ) : ℝ) ≤ (centralRationalLower (21 / 23) (2113 / 20) (309368812373 / 1000000000000) (18194355641 / 200000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers
