module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail150Floors : List ℕ := [
  3337821, 3269691
]

theorem l99PeriodTail150_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk150.filter selectedCellPredicate) l99PeriodTail150Floors = true := by decide +kernel

theorem l99PeriodTail150_sum : l99PeriodTail150Floors.sum = 6607512 := by decide +kernel

theorem l99PeriodTail150_lower : (6607512 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk150.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail150_checked
  simpa only [l99PeriodTail150_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
