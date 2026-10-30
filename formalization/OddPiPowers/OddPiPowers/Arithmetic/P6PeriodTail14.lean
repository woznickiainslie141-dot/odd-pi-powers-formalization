module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail14Floors : List ℕ := [
  202115538, 188856966, 176861586, 165973870, 156061515, 147011397, 246238107, 226532901, 209102056, 193608532, 179775492, 167373842, 130177233, 97421268, 68498214, 42897216, 20186635, 19666708, 36247970, 50267807, 62148597, 72233367, 67335542, 62919531, 58924145, 55297608, 51995873, 48981278, 1968817854, 48958779, 51971265, 55270619, 58894458, 62886774, 67299276, 72193074, 77640806, 83729349
]

theorem p6PeriodTail14_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk14.filter selectedCellPredicate) p6PeriodTail14Floors = true := by decide

theorem p6PeriodTail14_sum : p6PeriodTail14Floors.sum = 5752373048 := by decide

theorem p6PeriodTail14_lower : (5752373048 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk14.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail14_checked
  simpa only [p6PeriodTail14_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
