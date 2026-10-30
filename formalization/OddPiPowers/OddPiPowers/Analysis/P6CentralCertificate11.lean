module

public import OddPiPowers.Analysis.CentralNumericBounds

/-! Exact rational candidates, certified by finite-series inequalities. -/

@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem p6CentralInterval11_lower : ((20584952299 / 5000000000) : ℝ) ≤
    centralIntervalRate (47 / 69) (2113 / 20) := by
  have haQ : ((38670066597 / 125000000000) : ℚ) ≤ logSeries (21256986109 / 15600844800) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((383958902887 / 1000000000000) : ℚ) ≤ logSeries (69 / 47) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (21256986109 / 15600844800) (by norm_num) 10).1
  have hb := (logSeries_bounds (69 / 47) (by norm_num) 10).1
  have haQR : (((38670066597 / 125000000000) : ℚ) : ℝ) ≤ (logSeries (21256986109 / 15600844800) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((383958902887 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (69 / 47) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (47 / 69) (2113 / 20) (38670066597 / 125000000000) (383958902887 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((20584952299 / 5000000000) : ℚ) ≤ centralRationalLower (47 / 69) (2113 / 20) (38670066597 / 125000000000) (383958902887 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((20584952299 / 5000000000) : ℚ) : ℝ) ≤ (centralRationalLower (47 / 69) (2113 / 20) (38670066597 / 125000000000) (383958902887 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers
