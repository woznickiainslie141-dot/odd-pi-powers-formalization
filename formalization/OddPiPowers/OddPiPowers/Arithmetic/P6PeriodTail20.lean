module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail20Floors : List ℕ := [
  135924711, 114954734, 55532688, 207613409, 194898206, 214382983, 197452887, 219385787, 196150417, 52695996, 209956615, 230601076, 305337414, 282195344, 60172586, 254570797, 279196400, 59256567, 233506094, 165818600, 174697635, 121756467, 205831966, 67383955, 357124507, 268630071, 58908499, 83975118, 269239494, 130184637, 273166719, 216919178, 273758557, 178990952, 144183941, 170395505, 131916349, 84119195, 313415834, 73305476
]

theorem p6PeriodTail20_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk20.filter selectedCellPredicate) p6PeriodTail20Floors = true := by decide

theorem p6PeriodTail20_sum : p6PeriodTail20Floors.sum = 7267507366 := by decide

theorem p6PeriodTail20_lower : (7267507366 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk20.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail20_checked
  simpa only [p6PeriodTail20_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
