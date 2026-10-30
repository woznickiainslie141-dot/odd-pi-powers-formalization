module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval23_lower : ((4098930649 / 1250000000) : ℝ) ≤
    centralIntervalRate (53 / 99) (1801 / 20) := by
  have haQ : ((682972812441 / 1000000000000) : ℚ) ≤ logSeries (31790814301 / 16057958400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((624827936581 / 1000000000000) : ℚ) ≤ logSeries (99 / 53) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (31790814301 / 16057958400) (by norm_num) 10).1
  have hb := (logSeries_bounds (99 / 53) (by norm_num) 10).1
  have haQR : (((682972812441 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (31790814301 / 16057958400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((624827936581 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (99 / 53) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (53 / 99) (1801 / 20) (682972812441 / 1000000000000) (624827936581 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((4098930649 / 1250000000) : ℚ) ≤ centralRationalLower (53 / 99) (1801 / 20) (682972812441 / 1000000000000) (624827936581 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((4098930649 / 1250000000) : ℚ) : ℝ) ≤ (centralRationalLower (53 / 99) (1801 / 20) (682972812441 / 1000000000000) (624827936581 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
