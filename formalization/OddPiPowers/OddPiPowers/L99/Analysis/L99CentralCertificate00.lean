module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval00_lower : ((55003702081 / 10000000000) : ℝ) ≤
    centralIntervalRate (1 / 1) (1801 / 20) := by
  have haQ : ((341497402987 / 500000000000) : ℚ) ≤ logSeries (3243701 / 1638400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((0 / 1) : ℚ) ≤ logSeries (1 / 1) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (3243701 / 1638400) (by norm_num) 10).1
  have hb := (logSeries_bounds (1 / 1) (by norm_num) 10).1
  have haQR : (((341497402987 / 500000000000) : ℚ) : ℝ) ≤ (logSeries (3243701 / 1638400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((0 / 1) : ℚ) : ℝ) ≤ (logSeries (1 / 1) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (1 / 1) (1801 / 20) (341497402987 / 500000000000) (0 / 1)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((55003702081 / 10000000000) : ℚ) ≤ centralRationalLower (1 / 1) (1801 / 20) (341497402987 / 500000000000) (0 / 1) := by
    norm_num [centralRationalLower]
  have hqR : (((55003702081 / 10000000000) : ℚ) : ℝ) ≤ (centralRationalLower (1 / 1) (1801 / 20) (341497402987 / 500000000000) (0 / 1) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
