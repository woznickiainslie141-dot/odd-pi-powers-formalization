module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail25Floors : List ℕ := [
  102435059, 211267364, 133694066, 56890157, 176461824, 135959459, 107965989, 219525053, 67851516, 65662076, 41871128, 370845364, 499738861, 61369063, 78551643, 344408692, 142509388, 151355189, 199508829, 172452359, 218875932, 51396727, 222714742, 175546266, 37261455, 166146348, 127616425, 144155917, 106952074, 184316053, 69256272, 51666838, 443996316, 344247148, 60392192, 80111315, 332089639, 140275434, 154300091, 106856448
]

theorem p6PeriodTail25_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk25.filter selectedCellPredicate) p6PeriodTail25Floors = true := by decide

theorem p6PeriodTail25_sum : p6PeriodTail25Floors.sum = 6558496711 := by decide

theorem p6PeriodTail25_lower : (6558496711 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk25.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail25_checked
  simpa only [p6PeriodTail25_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
