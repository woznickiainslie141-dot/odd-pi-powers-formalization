module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail17Floors : List ℕ := [
  176673842, 271444157, 185719092, 172256933, 78547873, 174829816, 264886158, 61278254, 337022446, 289482249, 65541545, 352559573, 247155556, 210802490, 237145473, 198263210, 168219077, 167528104, 170626002, 141703288, 119559994, 81784715, 278407405, 92353497, 76150243, 76640795, 54334449, 673713329, 663744534, 52675534, 74108442, 73408621, 88701092, 341890220, 89672786, 132105003, 126403826, 153879200, 183929345, 179249063
]

theorem p6PeriodTail17_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk17.filter selectedCellPredicate) p6PeriodTail17Floors = true := by decide

theorem p6PeriodTail17_sum : p6PeriodTail17Floors.sum = 7584397231 := by decide

theorem p6PeriodTail17_lower : (7584397231 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk17.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail17_checked
  simpa only [p6PeriodTail17_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
