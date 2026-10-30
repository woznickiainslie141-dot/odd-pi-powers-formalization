module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail23Floors : List ℕ := [
  224421212, 102006770, 141919478, 162612254, 175999206, 54152527, 246582053, 210193709, 62609419, 144663478, 130751044, 227088312, 190455679, 129620414, 139519071, 176369322, 175149087, 122787427, 104728809, 323151841, 84774631, 70405295, 59403936, 40635427, 520108316, 543699722, 44563290, 65650726, 62818109, 367519180, 107965118, 126904311, 151306082, 146795701, 70158482, 157018905, 220904157, 218814074, 61309038, 243698984
]

theorem p6PeriodTail23_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk23.filter selectedCellPredicate) p6PeriodTail23Floors = true := by decide

theorem p6PeriodTail23_sum : p6PeriodTail23Floors.sum = 6609234596 := by decide

theorem p6PeriodTail23_lower : (6609234596 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk23.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail23_checked
  simpa only [p6PeriodTail23_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
