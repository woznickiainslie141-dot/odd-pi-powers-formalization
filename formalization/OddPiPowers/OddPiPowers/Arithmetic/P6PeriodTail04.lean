module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail04Floors : List ℕ := [
  211703143, 204087542, 185785438, 121472779, 352259546, 80337498, 62763051, 408840263, 379188388, 74917560, 80560030, 104055601, 336641947, 132445718, 166780628, 180379329, 87226690, 239142492, 259117835, 157037355, 282127786, 358072087, 364230619, 246605122, 112178160, 236158415, 191170224, 157919425, 159179589, 196127988, 158164511, 108542472, 274670346, 84895599, 81832926, 67175707, 682923573, 469253656, 59648229, 73152818
]

theorem p6PeriodTail04_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk4.filter selectedCellPredicate) p6PeriodTail04Floors = true := by decide

theorem p6PeriodTail04_sum : p6PeriodTail04Floors.sum = 8188772085 := by decide

theorem p6PeriodTail04_lower : (8188772085 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk4.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail04_checked
  simpa only [p6PeriodTail04_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
