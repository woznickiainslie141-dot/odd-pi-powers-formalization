module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval27_lower : ((14292780663 / 5000000000) : ℝ) ≤
    centralIntervalRate (5 / 11) (1801 / 20) := by
  have haQ : ((682970346317 / 1000000000000) : ℚ) ≤ logSeries (392478221 / 198246400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((9855717003 / 12500000000) : ℚ) ≤ logSeries (11 / 5) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (392478221 / 198246400) (by norm_num) 10).1
  have hb := (logSeries_bounds (11 / 5) (by norm_num) 10).1
  have haQR : (((682970346317 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (392478221 / 198246400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((9855717003 / 12500000000) : ℚ) : ℝ) ≤ (logSeries (11 / 5) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (5 / 11) (1801 / 20) (682970346317 / 1000000000000) (9855717003 / 12500000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((14292780663 / 5000000000) : ℚ) ≤ centralRationalLower (5 / 11) (1801 / 20) (682970346317 / 1000000000000) (9855717003 / 12500000000) := by
    norm_num [centralRationalLower]
  have hqR : (((14292780663 / 5000000000) : ℚ) : ℝ) ≤ (centralRationalLower (5 / 11) (1801 / 20) (682970346317 / 1000000000000) (9855717003 / 12500000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
