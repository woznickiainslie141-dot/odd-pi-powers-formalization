module
public import OddPiPowers.L99.Analysis.CentralNumericBounds
@[expose] public section
namespace OddPiPowers.L99
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem l99CentralInterval01_lower : ((54092479879 / 10000000000) : ℝ) ≤
    centralIntervalRate (97 / 99) (1801 / 20) := by
  have haQ : ((34149678647 / 50000000000) : ℚ) ≤ logSeries (31791474301 / 16057958400) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have hbQ : ((20408871631 / 1000000000000) : ℚ) ≤ logSeries (99 / 97) 10 := by
    norm_num [logSeries, Finset.sum_range_succ]
  have ha := (logSeries_bounds (31791474301 / 16057958400) (by norm_num) 10).1
  have hb := (logSeries_bounds (99 / 97) (by norm_num) 10).1
  have haQR : (((34149678647 / 50000000000) : ℚ) : ℝ) ≤ (logSeries (31791474301 / 16057958400) 10 : ℝ) := Rat.cast_le.mpr haQ
  have hbQR : (((20408871631 / 1000000000000) : ℚ) : ℝ) ≤ (logSeries (99 / 97) 10 : ℝ) := Rat.cast_le.mpr hbQ
  have haR := haQR.trans ha
  have hbR := hbQR.trans hb
  have ht := centralIntervalRate_from_logs (97 / 99) (1801 / 20) (34149678647 / 50000000000) (20408871631 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num at haR ⊢ <;> exact haR)
    (by norm_num at hbR ⊢ <;> exact hbR)
  have hq : ((54092479879 / 10000000000) : ℚ) ≤ centralRationalLower (97 / 99) (1801 / 20) (34149678647 / 50000000000) (20408871631 / 1000000000000) := by
    norm_num [centralRationalLower]
  have hqR : (((54092479879 / 10000000000) : ℚ) : ℝ) ≤ (centralRationalLower (97 / 99) (1801 / 20) (34149678647 / 50000000000) (20408871631 / 1000000000000) : ℝ) := Rat.cast_le.mpr hq
  have hfinal := hqR.trans ht
  norm_num at hfinal ⊢
  exact hfinal

end OddPiPowers.L99
