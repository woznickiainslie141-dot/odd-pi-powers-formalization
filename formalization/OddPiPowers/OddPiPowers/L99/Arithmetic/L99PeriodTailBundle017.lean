module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail085Floors : List ℕ := [
  101638620, 93065998, 177062292, 140683353, 62992057, 177842976, 136595637, 114863413, 90401889, 77993245, 138392012, 108583481, 94197787, 71968035, 60252005, 47244548,
  580417994, 562253433, 44221074, 56085042
]

theorem l99PeriodTail085_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk85.filter selectedCellPredicate) l99PeriodTail085Floors = true := by decide +kernel

theorem l99PeriodTail085_sum : l99PeriodTail085Floors.sum = 2936754891 := by decide +kernel

theorem l99PeriodTail085_lower : (2936754891 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk85.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail085_checked
  simpa only [l99PeriodTail085_sum, Nat.cast_ofNat] using h


def l99PeriodTail086Floors : List ℕ := [
  66553939, 80255773, 91084115, 114697542, 136456054, 92395656, 117610996, 140165154, 169895151, 134806545, 69599693, 81608564, 185186784, 149792245, 59424121, 128091080,
  142099581, 77041298, 259504208, 244754952
]

theorem l99PeriodTail086_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk86.filter selectedCellPredicate) l99PeriodTail086Floors = true := by decide +kernel

theorem l99PeriodTail086_sum : l99PeriodTail086Floors.sum = 2541023451 := by decide +kernel

theorem l99PeriodTail086_lower : (2541023451 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk86.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail086_checked
  simpa only [l99PeriodTail086_sum, Nat.cast_ofNat] using h


def l99PeriodTail087Floors : List ℕ := [
  67395490, 118615222, 101041752, 162968930, 192104329, 128599900, 89635581, 70078265, 111043625, 77308298, 56919005, 403534526, 324178496, 55113242, 81750869, 118769224,
  82127027, 106163445, 142560990, 54498421
]

theorem l99PeriodTail087_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk87.filter selectedCellPredicate) l99PeriodTail087Floors = true := by decide +kernel

theorem l99PeriodTail087_sum : l99PeriodTail087Floors.sum = 2544406637 := by decide +kernel

theorem l99PeriodTail087_lower : (2544406637 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk87.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail087_checked
  simpa only [l99PeriodTail087_sum, Nat.cast_ofNat] using h


def l99PeriodTail088Floors : List ℕ := [
  142509147, 188109707, 118589517, 130316862, 81175858, 48666642, 229016871, 267393154, 62268857, 100074330, 70983419, 110417865, 158732677, 74584516, 224033465, 184560570,
  61952813, 117583107, 109846425, 199348573
]

theorem l99PeriodTail088_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk88.filter selectedCellPredicate) l99PeriodTail088Floors = true := by decide +kernel

theorem l99PeriodTail088_sum : l99PeriodTail088Floors.sum = 2680164375 := by decide +kernel

theorem l99PeriodTail088_lower : (2680164375 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk88.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail088_checked
  simpa only [l99PeriodTail088_sum, Nat.cast_ofNat] using h


def l99PeriodTail089Floors : List ℕ := [
  176165988, 74416195, 76187555, 140469646, 171004405, 160218236, 129171552, 113792846, 92589051, 82738499, 74380549, 73339795, 127378589, 115735342, 98460608, 91306849,
  73773456, 64776351, 52920487, 47168065
]

theorem l99PeriodTail089_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk89.filter selectedCellPredicate) l99PeriodTail089Floors = true := by decide +kernel

theorem l99PeriodTail089_sum : l99PeriodTail089Floors.sum = 2035994064 := by decide +kernel

theorem l99PeriodTail089_lower : (2035994064 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk89.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail089_checked
  simpa only [l99PeriodTail089_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
