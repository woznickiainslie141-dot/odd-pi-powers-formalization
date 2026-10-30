module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail07Floors : List ℕ := [
  253236876, 221073784, 194672261, 327039590, 202879490, 174892314, 126935582, 89238092, 338724715, 70298192, 75538872, 65631495, 57553284, 50880058, 992101074, 510798878, 43239532, 61377661, 70304682, 81332016, 95174605, 617743715, 133791245, 152242706, 145661579, 135171011, 119006244, 152568415, 172573516, 196789346, 226486784, 126563061, 136892252, 87267548, 285067890, 271483695, 145867269, 130903694, 111369957, 226214522
]

theorem p6PeriodTail07_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk7.filter selectedCellPredicate) p6PeriodTail07Floors = true := by decide

theorem p6PeriodTail07_sum : p6PeriodTail07Floors.sum = 7676587502 := by decide

theorem p6PeriodTail07_lower : (7676587502 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk7.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail07_checked
  simpa only [p6PeriodTail07_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
