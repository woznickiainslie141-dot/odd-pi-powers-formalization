module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail035Floors : List ℕ := [
  203431339, 179085006, 114308301, 137525856, 79798293, 52112909, 229199859, 273403390, 69518343, 104457410, 80869682, 126050985, 112219669, 72276567, 94375943, 246208940,
  223822304, 70152474, 134203689, 126641660
]

theorem l99PeriodTail035_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk35.filter selectedCellPredicate) l99PeriodTail035Floors = true := by decide +kernel

theorem l99PeriodTail035_sum : l99PeriodTail035Floors.sum = 2729662619 := by decide +kernel

theorem l99PeriodTail035_lower : (2729662619 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk35.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail035_checked
  simpa only [l99PeriodTail035_sum, Nat.cast_ofNat] using h


def l99PeriodTail036Floors : List ℕ := [
  60682029, 159078863, 193308214, 96951291, 85179946, 171826785, 156719173, 73303487, 70216641, 131921159, 192805565, 171959503, 143297933, 119368897, 99241814, 82199589,
  75203293, 62157380, 110240346, 105296609
]

theorem l99PeriodTail036_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk36.filter selectedCellPredicate) l99PeriodTail036Floors = true := by decide +kernel

theorem l99PeriodTail036_sum : l99PeriodTail036Floors.sum = 2360958517 := by decide +kernel

theorem l99PeriodTail036_lower : (2360958517 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk36.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail036_checked
  simpa only [l99PeriodTail036_sum, Nat.cast_ofNat] using h


def l99PeriodTail037Floors : List ℕ := [
  100634960, 96270947, 92200834, 88411172, 79225126, 71400042, 64679727, 58865561, 53801643, 49364214, 1147669416, 562196930, 43959442, 47823842, 52221237, 57254371,
  63051993, 69777187, 77638969, 86908749
]

theorem l99PeriodTail037_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk37.filter selectedCellPredicate) l99PeriodTail037Floors = true := by decide +kernel

theorem l99PeriodTail037_sum : l99PeriodTail037Floors.sum = 2963356362 := by decide +kernel

theorem l99PeriodTail037_lower : (2963356362 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk37.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail037_checked
  simpa only [l99PeriodTail037_sum, Nat.cast_ofNat] using h


def l99PeriodTail038Floors : List ℕ := [
  97944092, 111223761, 127400605, 147383472, 82714489, 89753431, 105248571, 115038240, 126260406, 139208885, 154256894, 159606824, 165185353, 54635542, 126894477, 138299210,
  80077721, 77395902, 180110876, 198820827
]

theorem l99PeriodTail038_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk38.filter selectedCellPredicate) l99PeriodTail038Floors = true := by decide +kernel

theorem l99PeriodTail038_sum : l99PeriodTail038Floors.sum = 2477459578 := by decide +kernel

theorem l99PeriodTail038_lower : (2477459578 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk38.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail038_checked
  simpa only [l99PeriodTail038_sum, Nat.cast_ofNat] using h


def l99PeriodTail039Floors : List ℕ := [
  107361995, 113243893, 58980807, 172798338, 188504469, 61142472, 139753033, 136505777, 78179849, 44156907, 219725876, 239038261, 67931032, 108304429, 89630576, 150464496,
  146448787, 101616566, 141919953, 81738042
]

theorem l99PeriodTail039_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk39.filter selectedCellPredicate) l99PeriodTail039Floors = true := by decide +kernel

theorem l99PeriodTail039_sum : l99PeriodTail039Floors.sum = 2447445558 := by decide +kernel

theorem l99PeriodTail039_lower : (2447445558 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk39.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail039_checked
  simpa only [l99PeriodTail039_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
