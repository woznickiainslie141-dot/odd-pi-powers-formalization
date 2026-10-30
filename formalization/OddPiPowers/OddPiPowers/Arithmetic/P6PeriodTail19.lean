module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail19Floors : List ℕ := [
  272855268, 246441090, 121163543, 57784798, 163153969, 245478684, 219631775, 197662907, 143066579, 130057463, 89059178, 159939169, 176851215, 157554721, 169503653, 127356942, 115415296, 84062399, 515079153, 95857062, 85004258, 91074980, 68176920, 61578602, 44715176, 40769419, 883267031, 896312558, 52514064, 57678944, 76374238, 70587657, 78731576, 70696927, 540595061, 81500729, 111733224, 123093931, 136280127, 121364042
]

theorem p6PeriodTail19_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk19.filter selectedCellPredicate) p6PeriodTail19Floors = true := by decide

theorem p6PeriodTail19_sum : p6PeriodTail19Floors.sum = 7180024328 := by decide

theorem p6PeriodTail19_lower : (7180024328 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk19.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail19_checked
  simpa only [p6PeriodTail19_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
