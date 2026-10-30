module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail29Floors : List ℕ := [
  34987115, 50461588, 48556825, 62343882, 60076197, 72412537, 69871060, 80953289, 65173662, 63000649, 48747626, 47174732, 34257567, 33186760, 21443591, 20793634, 10086393, 9789667
]

theorem p6PeriodTail29_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk29.filter selectedCellPredicate) p6PeriodTail29Floors = true := by decide

theorem p6PeriodTail29_sum : p6PeriodTail29Floors.sum = 833316774 := by decide

theorem p6PeriodTail29_lower : (833316774 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk29.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail29_checked
  simpa only [p6PeriodTail29_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
