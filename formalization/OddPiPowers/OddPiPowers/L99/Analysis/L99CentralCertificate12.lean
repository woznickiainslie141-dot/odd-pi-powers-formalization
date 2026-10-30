module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval12_lower : ((2188636271 / 500000000) : ℝ) ≤
    centralIntervalRate (25 / 33) (1801 / 20) := by
  have haQ : ((682981670307 / 1000000000000) : ℚ) ≤ logSeries (3532343989 / 1784217600) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((138815868299 / 500000000000) : ℚ) ≤ logSeries (33 / 25) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (3532343989 / 1784217600) (by norm_num) 10).1
  have hb := (logSeries_bounds (33 / 25) (by norm_num) 10).1
  have haQR : (((682981670307 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (3532343989 / 1784217600) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((138815868299 / 500000000000) : ℚ) : ℝ) ≤ (logSeries (33 / 25) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (25 / 33) (1801 / 20) (682981670307 / 1000000000000) (138815868299 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((2188636271 / 500000000) : ℚ) ≤ centralRationalLower (25 / 33) (1801 / 20) (682981670307 / 1000000000000) (138815868299 / 500000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((2188636271 / 500000000) : ℚ) : ℝ) ≤ (centralRationalLower (25 / 33) (1801 / 20) (682981670307 / 1000000000000) (138815868299 / 500000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
