module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval09_lower : ((46644866223 / 10000000000) : ℝ) ≤
    centralIntervalRate (9 / 11) (1801 / 20) := by
  have haQ : ((682984614523 / 1000000000000) : ℚ) ≤ logSeries (392483821 / 198246400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((100335347731 / 500000000000) : ℚ) ≤ logSeries (11 / 9) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (392483821 / 198246400) (by norm_num) 10).1
  have hb := (logSeries_bounds (11 / 9) (by norm_num) 10).1
  have haQR : (((682984614523 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (392483821 / 198246400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((100335347731 / 500000000000) : ℚ) : ℝ) ≤ (logSeries (11 / 9) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (9 / 11) (1801 / 20) (682984614523 / 1000000000000) (100335347731 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((46644866223 / 10000000000) : ℚ) ≤ centralRationalLower (9 / 11) (1801 / 20) (682984614523 / 1000000000000) (100335347731 / 500000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((46644866223 / 10000000000) : ℚ) : ℝ) ≤ (centralRationalLower (9 / 11) (1801 / 20) (682984614523 / 1000000000000) (100335347731 / 500000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
