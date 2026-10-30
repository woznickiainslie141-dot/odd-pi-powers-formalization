module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail070Floors : List ℕ := [
  96996721, 63929265, 287185831, 274693125, 53510923, 79402870, 119244060, 102090600, 149944010, 134053244, 87544103, 107439547, 63427679, 246245205, 256274728, 67423774,
  102162472, 87047893, 138010700, 125335039
]

theorem l99PeriodTail070_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk70.filter selectedCellPredicate) l99PeriodTail070Floors = true := by decide +kernel

theorem l99PeriodTail070_sum : l99PeriodTail070Floors.sum = 2641961789 := by decide +kernel

theorem l99PeriodTail070_lower : (2641961789 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk70.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail070_checked
  simpa only [l99PeriodTail070_sum, Nat.cast_ofNat] using h


def l99PeriodTail071Floors : List ℕ := [
  82036832, 108642616, 59661287, 232362429, 222776613, 58439797, 89215716, 70290743, 111653402, 168262812, 82078638, 238415993, 227322846, 73441924, 143544394, 139257988,
  68081145, 198321325, 189879314, 61509611
]

theorem l99PeriodTail071_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk71.filter selectedCellPredicate) l99PeriodTail071Floors = true := by decide +kernel

theorem l99PeriodTail071_sum : l99PeriodTail071Floors.sum = 2625195425 := by decide +kernel

theorem l99PeriodTail071_lower : (2625195425 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk71.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail071_checked
  simpa only [l99PeriodTail071_sum, Nat.cast_ofNat] using h


def l99PeriodTail072Floors : List ℕ := [
  120455488, 117154278, 57381306, 154663365, 196841429, 102520345, 92237652, 192444317, 183167273, 88311879, 86233380, 166518028, 159032101, 76864825, 75175053, 145498880,
  139371100, 67507345, 66115104, 128222284
]

theorem l99PeriodTail072_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk72.filter selectedCellPredicate) l99PeriodTail072Floors = true := by decide +kernel

theorem l99PeriodTail072_sum : l99PeriodTail072Floors.sum = 2415715432 := by decide +kernel

theorem l99PeriodTail072_lower : (2415715432 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk72.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail072_checked
  simpa only [l99PeriodTail072_sum, Nat.cast_ofNat] using h


def l99PeriodTail073Floors : List ℕ := [
  196972624, 185714533, 175394820, 154061159, 134724009, 117162560, 101184807, 86623220, 73331144, 61179802, 50055778, 39858909, 38125619, 29202386, 27985421, 20132233,
  37895605, 46713518, 54144611, 60413362
]

theorem l99PeriodTail073_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk73.filter selectedCellPredicate) l99PeriodTail073Floors = true := by decide +kernel

theorem l99PeriodTail073_sum : l99PeriodTail073Floors.sum = 1690876120 := by decide +kernel

theorem l99PeriodTail073_lower : (1690876120 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk73.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail073_checked
  simpa only [l99PeriodTail073_sum, Nat.cast_ofNat] using h


def l99PeriodTail074Floors : List ℕ := [
  65703165, 70164810, 73923018, 77081514, 79727005, 81932320, 83758899, 79168880, 74946100, 71052401, 67454455, 64123050, 61032491, 58160110, 55485842, 52991877,
  50662364, 48483155, 46441591, 44526320
]

theorem l99PeriodTail074_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk74.filter selectedCellPredicate) l99PeriodTail074Floors = true := by decide +kernel

theorem l99PeriodTail074_sum : l99PeriodTail074Floors.sum = 1306819367 := by decide +kernel

theorem l99PeriodTail074_lower : (1306819367 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk74.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail074_checked
  simpa only [l99PeriodTail074_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
