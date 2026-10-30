module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail030Floors : List ℕ := [
  40114041, 663682048, 643528836, 58189485, 60919904, 68172001, 72000960, 81730405, 87336527, 100982187, 109661404, 129967886, 144452528, 83874871, 101189209, 113379754,
  137754017, 156622801, 179653430, 125544335
]

theorem l99PeriodTail030_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk30.filter selectedCellPredicate) l99PeriodTail030Floors = true := by decide +kernel

theorem l99PeriodTail030_sum : l99PeriodTail030Floors.sum = 3158756629 := by decide +kernel

theorem l99PeriodTail030_lower : (3158756629 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk30.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail030_checked
  simpa only [l99PeriodTail030_sum, Nat.cast_ofNat] using h


def l99PeriodTail031Floors : List ℕ := [
  72965401, 76930505, 167123448, 187502006, 95266214, 109255540, 241269661, 174984032, 67903585, 143701779, 143343567, 76095279, 248307589, 242095188, 64785279, 112127613,
  86454278, 147582211, 168866150, 110095505
]

theorem l99PeriodTail031_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk31.filter selectedCellPredicate) l99PeriodTail031Floors = true := by decide +kernel

theorem l99PeriodTail031_sum : l99PeriodTail031Floors.sum = 2736654830 := by decide +kernel

theorem l99PeriodTail031_lower : (2736654830 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk31.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail031_checked
  simpa only [l99PeriodTail031_sum, Nat.cast_ofNat] using h


def l99PeriodTail032Floors : List ℕ := [
  144386149, 97441268, 66785200, 357772490, 293465102, 56339543, 80608465, 124863116, 99322113, 136902309, 115327538, 71118143, 83113487, 216815317, 230709804, 89056101,
  86496415, 148664383, 177173163, 138279833
]

theorem l99PeriodTail032_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk32.filter selectedCellPredicate) l99PeriodTail032Floors = true := by decide +kernel

theorem l99PeriodTail032_sum : l99PeriodTail032Floors.sum = 2814639939 := by decide +kernel

theorem l99PeriodTail032_lower : (2814639939 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk32.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail032_checked
  simpa only [l99PeriodTail032_sum, Nat.cast_ofNat] using h


def l99PeriodTail033Floors : List ℕ := [
  102393900, 83962353, 129500116, 103154774, 72960113, 57689081, 42861790, 446792600, 451528983, 47807966, 64058199, 81267414, 106487575, 134403750, 87588159, 116235851,
  145702643, 188001022, 158903527, 85793244
]

theorem l99PeriodTail033_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk33.filter selectedCellPredicate) l99PeriodTail033Floors = true := by decide +kernel

theorem l99PeriodTail033_sum : l99PeriodTail033Floors.sum = 2707093060 := by decide +kernel

theorem l99PeriodTail033_lower : (2707093060 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk33.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail033_checked
  simpa only [l99PeriodTail033_sum, Nat.cast_ofNat] using h


def l99PeriodTail034Floors : List ℕ := [
  104095022, 56876313, 193894670, 219756266, 84817142, 78900941, 128494803, 131470621, 95863095, 130435454, 91656533, 59321117, 337668525, 309225031, 53107985, 67494774,
  98830956, 68881705, 112132275, 141930574
]

theorem l99PeriodTail034_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk34.filter selectedCellPredicate) l99PeriodTail034Floors = true := by decide +kernel

theorem l99PeriodTail034_sum : l99PeriodTail034Floors.sum = 2564853802 := by decide +kernel

theorem l99PeriodTail034_lower : (2564853802 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk34.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail034_checked
  simpa only [l99PeriodTail034_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
