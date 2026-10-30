module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail03Floors : List ℕ := [
  139490673, 164673298, 57020273, 180060900, 182784520, 59112244, 174167026, 100746840, 256438603, 65109631, 318303588, 328553118, 41842642, 283515619, 115583159, 102180294, 232455459, 269562930, 274123225, 208655171, 164138550, 189604469, 119697498, 226686101, 82022508, 61831739, 440535871, 272695844, 52884567, 70887067, 251527763, 109457748, 110645054, 228540041, 297525549, 88964278, 314334204, 273442116, 78875936, 268707565
]

theorem p6PeriodTail03_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk3.filter selectedCellPredicate) p6PeriodTail03Floors = true := by decide

theorem p6PeriodTail03_sum : p6PeriodTail03Floors.sum = 7257383681 := by decide

theorem p6PeriodTail03_lower : (7257383681 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk3.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail03_checked
  simpa only [p6PeriodTail03_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
