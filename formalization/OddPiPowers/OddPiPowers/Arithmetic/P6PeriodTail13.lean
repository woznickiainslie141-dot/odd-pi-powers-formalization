module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail13Floors : List ℕ := [
  113064277, 205249915, 57199501, 330474960, 310120908, 62299141, 68926003, 216032224, 140045261, 159572341, 67065587, 197169680, 222293221, 143411363, 275991241, 66840047, 322038863, 303082330, 58488113, 337040948, 160088960, 154836777, 222959148, 71958896, 276758326, 260225801, 62645556, 182486144, 140772114, 334931387, 260492492, 194942439, 46660719, 120538292, 86712005, 56055416, 121176346, 150894125, 186553771, 216821117
]

theorem p6PeriodTail13_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk13.filter selectedCellPredicate) p6PeriodTail13Floors = true := by decide

theorem p6PeriodTail13_sum : p6PeriodTail13Floors.sum = 6964915755 := by decide

theorem p6PeriodTail13_lower : (6964915755 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk13.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail13_checked
  simpa only [p6PeriodTail13_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
