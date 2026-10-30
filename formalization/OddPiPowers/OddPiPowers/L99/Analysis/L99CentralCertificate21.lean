module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval21_lower : ((17423677539 / 5000000000) : ℝ) ≤
    centralIntervalRate (19 / 33) (1801 / 20) := by
  have haQ : ((85371774561 / 125000000000) : ℚ) ≤ logSeries (3532317589 / 1784217600) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((552068582299 / 1000000000000) : ℚ) ≤ logSeries (33 / 19) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (3532317589 / 1784217600) (by norm_num) 10).1
  have hb := (logSeries_bounds (33 / 19) (by norm_num) 10).1
  have haQR : (((85371774561 / 125000000000) : ℚ) : ℝ) ≤ (logSeries (3532317589 / 1784217600) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((552068582299 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (33 / 19) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (19 / 33) (1801 / 20) (85371774561 / 125000000000) (552068582299 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((17423677539 / 5000000000) : ℚ) ≤ centralRationalLower (19 / 33) (1801 / 20) (85371774561 / 125000000000) (552068582299 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((17423677539 / 5000000000) : ℚ) : ℝ) ≤ (centralRationalLower (19 / 33) (1801 / 20) (85371774561 / 125000000000) (552068582299 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
