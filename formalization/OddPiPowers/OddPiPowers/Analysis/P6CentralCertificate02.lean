module

public import OddPiPowers.Analysis.CentralNumericBounds

/-! Exact rational candidates, certified by finite-series inequalities. -/

@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem p6CentralInterval02_lower : ((53882685337 / 10000000000) : ℝ) ≤
    centralIntervalRate (65 / 69) (2113 / 20) := by
  have haQ : ((9667813021 / 31250000000) : ℚ) ≤ logSeries (21257187709 / 15600844800) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((59719234701 / 1000000000000) : ℚ) ≤ logSeries (69 / 65) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (21257187709 / 15600844800) (by norm_num) 10).1
  have hb := (logSeries_bounds (69 / 65) (by norm_num) 10).1
  have haQR : (((9667813021 / 31250000000) : ℚ) : ℝ) ≤ (logSeries (21257187709 / 15600844800) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((59719234701 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (69 / 65) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (65 / 69) (2113 / 20) (9667813021 / 31250000000) (59719234701 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((53882685337 / 10000000000) : ℚ) ≤ centralRationalLower (65 / 69) (2113 / 20) (9667813021 / 31250000000) (59719234701 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((53882685337 / 10000000000) : ℚ) : ℝ) ≤ (centralRationalLower (65 / 69) (2113 / 20) (9667813021 / 31250000000) (59719234701 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers
