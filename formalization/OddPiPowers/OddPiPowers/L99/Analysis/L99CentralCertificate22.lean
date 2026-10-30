module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval22_lower : ((8455768501 / 2500000000) : ℝ) ≤
    centralIntervalRate (5 / 9) (1801 / 20) := by
  have haQ : ((682973491883 / 1000000000000) : ℚ) ≤ logSeries (262734181 / 132710400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((587786664901 / 1000000000000) : ℚ) ≤ logSeries (9 / 5) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (262734181 / 132710400) (by norm_num) 10).1
  have hb := (logSeries_bounds (9 / 5) (by norm_num) 10).1
  have haQR : (((682973491883 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (262734181 / 132710400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((587786664901 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (9 / 5) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (5 / 9) (1801 / 20) (682973491883 / 1000000000000) (587786664901 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((8455768501 / 2500000000) : ℚ) ≤ centralRationalLower (5 / 9) (1801 / 20) (682973491883 / 1000000000000) (587786664901 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((8455768501 / 2500000000) : ℚ) : ℝ) ≤ (centralRationalLower (5 / 9) (1801 / 20) (682973491883 / 1000000000000) (587786664901 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
