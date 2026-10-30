module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval16_lower : ((9966748531 / 2500000000) : ℝ) ≤
    centralIntervalRate (67 / 99) (1801 / 20) := by
  have haQ : ((682978096973 / 1000000000000) : ℚ) ≤ logSeries (31790982301 / 16057958400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((390427230743 / 1000000000000) : ℚ) ≤ logSeries (99 / 67) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (31790982301 / 16057958400) (by norm_num) 10).1
  have hb := (logSeries_bounds (99 / 67) (by norm_num) 10).1
  have haQR : (((682978096973 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (31790982301 / 16057958400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((390427230743 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (99 / 67) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (67 / 99) (1801 / 20) (682978096973 / 1000000000000) (390427230743 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((9966748531 / 2500000000) : ℚ) ≤ centralRationalLower (67 / 99) (1801 / 20) (682978096973 / 1000000000000) (390427230743 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((9966748531 / 2500000000) : ℚ) : ℝ) ≤ (centralRationalLower (67 / 99) (1801 / 20) (682978096973 / 1000000000000) (390427230743 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
