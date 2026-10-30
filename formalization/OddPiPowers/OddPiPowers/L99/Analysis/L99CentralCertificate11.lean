module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval11_lower : ((22367654581 / 5000000000) : ℝ) ≤
    centralIntervalRate (7 / 9) (1801 / 20) := by
  have haQ : ((682982626549 / 1000000000000) : ℚ) ≤ logSeries (262736581 / 132710400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((6282860707 / 25000000000) : ℚ) ≤ logSeries (9 / 7) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (262736581 / 132710400) (by norm_num) 10).1
  have hb := (logSeries_bounds (9 / 7) (by norm_num) 10).1
  have haQR : (((682982626549 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (262736581 / 132710400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((6282860707 / 25000000000) : ℚ) : ℝ) ≤ (logSeries (9 / 7) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (7 / 9) (1801 / 20) (682982626549 / 1000000000000) (6282860707 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((22367654581 / 5000000000) : ℚ) ≤ centralRationalLower (7 / 9) (1801 / 20) (682982626549 / 1000000000000) (6282860707 / 25000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((22367654581 / 5000000000) : ℚ) : ℝ) ≤ (centralRationalLower (7 / 9) (1801 / 20) (682982626549 / 1000000000000) (6282860707 / 25000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
