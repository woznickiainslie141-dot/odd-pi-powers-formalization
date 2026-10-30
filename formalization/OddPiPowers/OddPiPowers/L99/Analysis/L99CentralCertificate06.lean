module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval06_lower : ((49472073429 / 10000000000) : ℝ) ≤
    centralIntervalRate (29 / 33) (1801 / 20) := by
  have haQ : ((85373473151 / 125000000000) : ℚ) ≤ logSeries (3532365589 / 1784217600) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((3230293287 / 25000000000) : ℚ) ≤ logSeries (33 / 29) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (3532365589 / 1784217600) (by norm_num) 10).1
  have hb := (logSeries_bounds (33 / 29) (by norm_num) 10).1
  have haQR : (((85373473151 / 125000000000) : ℚ) : ℝ) ≤ (logSeries (3532365589 / 1784217600) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((3230293287 / 25000000000) : ℚ) : ℝ) ≤ (logSeries (33 / 29) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (29 / 33) (1801 / 20) (85373473151 / 125000000000) (3230293287 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((49472073429 / 10000000000) : ℚ) ≤ centralRationalLower (29 / 33) (1801 / 20) (85373473151 / 125000000000) (3230293287 / 25000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((49472073429 / 10000000000) : ℚ) : ℝ) ≤ (centralRationalLower (29 / 33) (1801 / 20) (85373473151 / 125000000000) (3230293287 / 25000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
