module

public import OddPiPowers.Analysis.CentralNumericBounds

/-! Exact rational candidates, certified by finite-series inequalities. -/

@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem p6CentralInterval04_lower : ((5112831961 / 1000000000) : ℝ) ≤
    centralIntervalRate (61 / 69) (2113 / 20) := by
  have haQ : ((154683822853 / 500000000000) : ℚ) ≤ logSeries (21257137309 / 15600844800) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((123232640423 / 1000000000000) : ℚ) ≤ logSeries (69 / 61) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (21257137309 / 15600844800) (by norm_num) 10).1
  have hb := (logSeries_bounds (69 / 61) (by norm_num) 10).1
  have haQR : (((154683822853 / 500000000000) : ℚ) : ℝ) ≤ (logSeries (21257137309 / 15600844800) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((123232640423 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (69 / 61) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (61 / 69) (2113 / 20) (154683822853 / 500000000000) (123232640423 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((5112831961 / 1000000000) : ℚ) ≤ centralRationalLower (61 / 69) (2113 / 20) (154683822853 / 500000000000) (123232640423 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((5112831961 / 1000000000) : ℚ) : ℝ) ≤ (centralRationalLower (61 / 69) (2113 / 20) (154683822853 / 500000000000) (123232640423 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers
