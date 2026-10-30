module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval24_lower : ((124031997 / 39062500) : ℝ) ≤
    centralIntervalRate (17 / 33) (1801 / 20) := by
  have haQ : ((170743039541 / 250000000000) : ℚ) ≤ logSeries (3532310389 / 1784217600) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((331647108703 / 500000000000) : ℚ) ≤ logSeries (33 / 17) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (3532310389 / 1784217600) (by norm_num) 10).1
  have hb := (logSeries_bounds (33 / 17) (by norm_num) 10).1
  have haQR : (((170743039541 / 250000000000) : ℚ) : ℝ) ≤ (logSeries (3532310389 / 1784217600) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((331647108703 / 500000000000) : ℚ) : ℝ) ≤ (logSeries (33 / 17) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (17 / 33) (1801 / 20) (170743039541 / 250000000000) (331647108703 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((124031997 / 39062500) : ℚ) ≤ centralRationalLower (17 / 33) (1801 / 20) (170743039541 / 250000000000) (331647108703 / 500000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((124031997 / 39062500) : ℚ) : ℝ) ≤ (centralRationalLower (17 / 33) (1801 / 20) (170743039541 / 250000000000) (331647108703 / 500000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
