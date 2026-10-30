module

public import OddPiPowers.Analysis.CentralNumericBounds

/-! Exact rational candidates, certified by finite-series inequalities. -/

@[expose] public section
namespace OddPiPowers
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem p6CentralInterval00_lower : ((56601354751 / 10000000000) : ℝ) ≤
    centralIntervalRate (1 / 1) (2113 / 20) := by
  have haQ : ((309372538169 / 1000000000000) : ℚ) ≤ logSeries (4464869 / 3276800) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((0 / 1) : ℚ) ≤ logSeries (1 / 1) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (4464869 / 3276800) (by norm_num) 10).1
  have hb := (logSeries_bounds (1 / 1) (by norm_num) 10).1
  have haQR : (((309372538169 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (4464869 / 3276800) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((0 / 1) : ℚ) : ℝ) ≤ (logSeries (1 / 1) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (1 / 1) (2113 / 20) (309372538169 / 1000000000000) (0 / 1)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((56601354751 / 10000000000) : ℚ) ≤ centralRationalLower (1 / 1) (2113 / 20) (309372538169 / 1000000000000) (0 / 1) := by
    norm_num [centralRationalLower]
  have hqR : (((56601354751 / 10000000000) : ℚ) : ℝ) ≤ (centralRationalLower (1 / 1) (2113 / 20) (309372538169 / 1000000000000) (0 / 1) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers
