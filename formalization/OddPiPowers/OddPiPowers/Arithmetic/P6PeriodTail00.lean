module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail00Floors : List ℕ := [
  58791255, 60545802, 72776763, 75015502, 88410463, 91216438, 94158151, 85088938, 87924487, 77917866, 80603954, 69526147, 72008520, 59701006, 61911505, 48185317, 50038033, 34666466, 36052685, 18761873, 19543360, 117528088, 121034730, 145484135, 149958387, 176734017, 182341798, 188220784, 170090156, 175756833, 155752706, 161120554, 138975636, 143936242, 119333817, 123750994, 96313537
]

theorem p6PeriodTail00_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk0.filter selectedCellPredicate) p6PeriodTail00Floors = true := by decide

theorem p6PeriodTail00_sum : p6PeriodTail00Floors.sum = 3709176945 := by decide

theorem p6PeriodTail00_lower : (3709176945 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk0.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail00_checked
  simpa only [p6PeriodTail00_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
