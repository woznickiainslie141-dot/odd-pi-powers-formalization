module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail060Floors : List ℕ := [
  38209293, 646062645, 717949244, 42564711, 47457030, 57681273, 65172042, 79932807, 85300910, 99058427, 107479516, 128147409, 67632791, 102037213, 113501261, 127012308,
  133549305, 151594980, 161165895, 186345601
]

theorem l99PeriodTail060_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk60.filter selectedCellPredicate) l99PeriodTail060Floors = true := by decide +kernel

theorem l99PeriodTail060_sum : l99PeriodTail060Floors.sum = 3157854661 := by decide +kernel

theorem l99PeriodTail060_lower : (3157854661 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk60.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail060_checked
  simpa only [l99PeriodTail060_sum, Nat.cast_ofNat] using h


def l99PeriodTail061Floors : List ℕ := [
  130424542, 76632993, 81087913, 177190364, 200502003, 101980973, 118258596, 62307864, 201082454, 207974399, 75006285, 172929483, 102496367, 77329294, 100633330, 62615905,
  248193851, 230278410, 53011398, 81620306
]

theorem l99PeriodTail061_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk61.filter selectedCellPredicate) l99PeriodTail061Floors = true := by decide +kernel

theorem l99PeriodTail061_sum : l99PeriodTail061Floors.sum = 2561556730 := by decide +kernel

theorem l99PeriodTail061_lower : (2561556730 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk61.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail061_checked
  simpa only [l99PeriodTail061_sum, Nat.cast_ofNat] using h


def l99PeriodTail062Floors : List ℕ := [
  141947150, 119234421, 189128240, 143277157, 63923161, 154349857, 106730268, 76213227, 119399805, 88505469, 64638476, 414756527, 318708685, 52811614, 77706241, 111613615,
  76306722, 97600975, 129254229, 165494785
]

theorem l99PeriodTail062_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk62.filter selectedCellPredicate) l99PeriodTail062Floors = true := by decide +kernel

theorem l99PeriodTail062_sum : l99PeriodTail062Floors.sum = 2711600624 := by decide +kernel

theorem l99PeriodTail062_lower : (2711600624 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk62.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail062_checked
  simpa only [l99PeriodTail062_sum, Nat.cast_ofNat] using h


def l99PeriodTail063Floors : List ℕ := [
  151190792, 93737344, 110038566, 62521467, 208128190, 240721937, 77418688, 131809175, 128713732, 59712128, 163058659, 171762675, 81998858, 75759360, 135447463, 183829610,
  151657629, 118162291, 100562815, 162016249
]

theorem l99PeriodTail063_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk63.filter selectedCellPredicate) l99PeriodTail063Floors = true := by decide +kernel

theorem l99PeriodTail063_sum : l99PeriodTail063Floors.sum = 2608247628 := by decide +kernel

theorem l99PeriodTail063_lower : (2608247628 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk63.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail063_checked
  simpa only [l99PeriodTail063_sum, Nat.cast_ofNat] using h


def l99PeriodTail064Floors : List ℕ := [
  124830828, 106754866, 80624790, 66859206, 52007782, 44423137, 564794267, 582985839, 51405360, 60514913, 77841439, 87849088, 109053223, 128296699, 78327843, 98354162,
  115352709, 147726789, 165836370, 63256620
]

theorem l99PeriodTail064_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk64.filter selectedCellPredicate) l99PeriodTail064Floors = true := by decide +kernel

theorem l99PeriodTail064_sum : l99PeriodTail064Floors.sum = 2807095930 := by decide +kernel

theorem l99PeriodTail064_lower : (2807095930 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk64.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail064_checked
  simpa only [l99PeriodTail064_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
