module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail26Floors : List ℕ := [
  169789532, 223050791, 219326584, 129685350, 99755987, 112836671, 276759895, 54457649, 320684674, 310646365, 50831457, 250240675, 122882352, 135952196, 72094658, 178336336, 175670309, 83441985, 192776698, 113395913, 161064984, 77346104, 54926442, 324057537, 293231538, 71868301, 282829620, 138691261, 163783894, 200861420, 131812281, 258735656, 50949888, 312638924, 303293531, 71488828, 234786972, 115331165, 170486187, 201051435
]

theorem p6PeriodTail26_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk26.filter selectedCellPredicate) p6PeriodTail26Floors = true := by decide

theorem p6PeriodTail26_sum : p6PeriodTail26Floors.sum = 6911852045 := by decide

theorem p6PeriodTail26_lower : (6911852045 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk26.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail26_checked
  simpa only [p6PeriodTail26_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
