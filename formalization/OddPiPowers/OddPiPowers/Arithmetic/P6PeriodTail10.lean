module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail10Floors : List ℕ := [
  58091245, 520193295, 106110283, 116545569, 154319799, 142626237, 159079799, 142843839, 161471407, 209785412, 196937142, 216625706, 199518445, 221680719, 198202224, 164655157, 72892808, 152837380, 248677662, 275311745, 193944033, 64036770, 201111802, 142115642, 119281552, 237922275, 100089221, 56813380, 299554095, 328068851, 69397277, 291461308, 123718543, 68226089, 175948528, 184064658, 259046044, 135786566, 287538199, 75537429
]

theorem p6PeriodTail10_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk10.filter selectedCellPredicate) p6PeriodTail10Floors = true := by decide

theorem p6PeriodTail10_sum : p6PeriodTail10Floors.sum = 7132068135 := by decide

theorem p6PeriodTail10_lower : (7132068135 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk10.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail10_checked
  simpa only [p6PeriodTail10_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
