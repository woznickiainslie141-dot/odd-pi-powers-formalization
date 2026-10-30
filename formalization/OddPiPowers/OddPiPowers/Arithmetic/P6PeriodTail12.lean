module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail12Floors : List ℕ := [
  171033775, 171611804, 210608933, 169173235, 239253206, 238464130, 211961529, 298198471, 295374195, 65889524, 349205881, 282307021, 61592798, 319480578, 146424429, 65783925, 173112740, 223959050, 272761993, 147934414, 116552260, 234089847, 89406960, 68886577, 54703580, 381348124, 498652454, 72215847, 76699113, 331971877, 135440369, 142678377, 186098010, 190895993, 199568146, 257767389, 248714228, 180877714, 137464044, 153770248
]

theorem p6PeriodTail12_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk12.filter selectedCellPredicate) p6PeriodTail12Floors = true := by decide

theorem p6PeriodTail12_sum : p6PeriodTail12Floors.sum = 7871932788 := by decide

theorem p6PeriodTail12_lower : (7871932788 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk12.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail12_checked
  simpa only [p6PeriodTail12_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
