module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail09Floors : List ℕ := [
  201424789, 283631080, 89967066, 339098269, 309166311, 60895056, 342683989, 257471493, 233325640, 169939419, 53313301, 248049558, 221931882, 199732884, 144564769, 131419390, 89991761, 56164217, 193763023, 171823252, 184092211, 165367647, 149361624, 112976813, 103006736, 546536712, 89332971, 79586628, 85623343, 64333877, 58302082, 42464474, 905834698, 892375209, 41183232, 56460463, 62201696, 68865540, 61328696, 68687369
]

theorem p6PeriodTail09_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk9.filter selectedCellPredicate) p6PeriodTail09Floors = true := by decide

theorem p6PeriodTail09_sum : p6PeriodTail09Floors.sum = 7636279170 := by decide

theorem p6PeriodTail09_lower : (7636279170 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk9.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail09_checked
  simpa only [p6PeriodTail09_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
