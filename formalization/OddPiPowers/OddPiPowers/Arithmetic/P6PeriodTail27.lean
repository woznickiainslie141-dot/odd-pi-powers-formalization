module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail27Floors : List ℕ := [
  245960165, 80595300, 378787557, 305293832, 74763876, 264803428, 144167127, 141875960, 208636072, 82148883, 268557412, 260409805, 51098139, 188754762, 123503542, 121685255, 143364379, 58868464, 231264337, 279941693, 324333926, 261106724, 252394225, 195288514, 188982622, 91975772, 60342941, 177253757, 128845968, 42071326, 110488764, 81207709, 39997269, 117636896, 114224086, 37341838, 145841468, 187247080, 180432374, 217478804
]

theorem p6PeriodTail27_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk27.filter selectedCellPredicate) p6PeriodTail27Floors = true := by decide

theorem p6PeriodTail27_sum : p6PeriodTail27Floors.sum = 6608972051 := by decide

theorem p6PeriodTail27_lower : (6608972051 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk27.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail27_checked
  simpa only [p6PeriodTail27_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
