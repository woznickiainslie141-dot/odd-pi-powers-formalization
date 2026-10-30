module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail055Floors : List ℕ := [
  141520891, 193409418, 160450360, 98233866, 123633943, 64276059, 230037842, 258102951, 75444520, 137767136, 122668151, 208987545, 171414268, 74647449, 68490585, 121325303,
  150877339, 113359253, 86224651, 66089723
]

theorem l99PeriodTail055_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk55.filter selectedCellPredicate) l99PeriodTail055Floors = true := by decide +kernel

theorem l99PeriodTail055_sum : l99PeriodTail055Floors.sum = 2666961253 := by decide +kernel

theorem l99PeriodTail055_lower : (2666961253 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk55.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail055_checked
  simpa only [l99PeriodTail055_sum, Nat.cast_ofNat] using h


def l99PeriodTail056Floors : List ℕ := [
  115824059, 96178661, 81965011, 66164154, 54530646, 45717437, 560026551, 425809236, 44082763, 58082819, 77513493, 97844248, 127381043, 79287576, 93382531, 111602642,
  135731665, 168634357, 60625900, 149472978
]

theorem l99PeriodTail056_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk56.filter selectedCellPredicate) l99PeriodTail056Floors = true := by decide +kernel

theorem l99PeriodTail056_sum : l99PeriodTail056Floors.sum = 2649857770 := by decide +kernel

theorem l99PeriodTail056_lower : (2649857770 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk56.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail056_checked
  simpa only [l99PeriodTail056_sum, Nat.cast_ofNat] using h


def l99PeriodTail057Floors : List ℕ := [
  179743733, 104250238, 115995771, 63040750, 196740493, 186596280, 55855574, 90930779, 77648215, 136073550, 138010419, 99836345, 146009242, 94005091, 65584549, 44640105,
  319916271, 329905492, 51671194, 76314022
]

theorem l99PeriodTail057_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk57.filter selectedCellPredicate) l99PeriodTail057Floors = true := by decide +kernel

theorem l99PeriodTail057_sum : l99PeriodTail057Floors.sum = 2572768113 := by decide +kernel

theorem l99PeriodTail057_lower : (2572768113 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk57.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail057_checked
  simpa only [l99PeriodTail057_sum, Nat.cast_ofNat] using h


def l99PeriodTail058Floors : List ℕ := [
  103185820, 164157589, 124758395, 177074398, 166005080, 96943881, 125398945, 72288260, 289767122, 222223104, 56276643, 90614427, 170176625, 156879623, 68244117, 205719206,
  170315353, 57346646, 109070380, 102166370
]

theorem l99PeriodTail058_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk58.filter selectedCellPredicate) l99PeriodTail058Floors = true := by decide +kernel

theorem l99PeriodTail058_sum : l99PeriodTail058Floors.sum = 2728611984 := by decide +kernel

theorem l99PeriodTail058_lower : (2728611984 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk58.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail058_checked
  simpa only [l99PeriodTail058_sum, Nat.cast_ofNat] using h


def l99PeriodTail059Floors : List ℕ := [
  200401066, 165175877, 75817739, 77306360, 132691486, 175673990, 164292245, 133721420, 118171284, 97093416, 86978858, 136894636, 123590004, 103971568, 96071004, 82910027,
  72280109, 58681231, 52012672, 42551413
]

theorem l99PeriodTail059_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk59.filter selectedCellPredicate) l99PeriodTail059Floors = true := by decide +kernel

theorem l99PeriodTail059_sum : l99PeriodTail059Floors.sum = 2196286405 := by decide +kernel

theorem l99PeriodTail059_lower : (2196286405 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk59.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail059_checked
  simpa only [l99PeriodTail059_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
