module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail080Floors : List ℕ := [
  296971887, 310463430, 63792946, 104233991, 164314077, 134226876, 58300135, 159202965, 150877677, 61225229, 155991013, 105204967, 79877282, 113258001, 82329260, 55075596,
  338921662, 354144752, 65236161, 85575758
]

theorem l99PeriodTail080_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk80.filter selectedCellPredicate) l99PeriodTail080Floors = true := by decide +kernel

theorem l99PeriodTail080_sum : l99PeriodTail080Floors.sum = 2939223665 := by decide +kernel

theorem l99PeriodTail080_lower : (2939223665 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk80.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail080_checked
  simpa only [l99PeriodTail080_sum, Nat.cast_ofNat] using h


def l99PeriodTail081Floors : List ℕ := [
  130074084, 94190774, 137074814, 112995770, 68537944, 79019774, 216289001, 189854877, 83663939, 73873035, 124527890, 133396032, 101495997, 132210552, 97566172, 64529078,
  48755055, 318312415, 354398936, 49106795
]

theorem l99PeriodTail081_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk81.filter selectedCellPredicate) l99PeriodTail081Floors = true := by decide +kernel

theorem l99PeriodTail081_sum : l99PeriodTail081Floors.sum = 2609872934 := by decide +kernel

theorem l99PeriodTail081_lower : (2609872934 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk81.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail081_checked
  simpa only [l99PeriodTail081_sum, Nat.cast_ofNat] using h


def l99PeriodTail082Floors : List ℕ := [
  63511182, 85342668, 111477211, 75099859, 102665556, 133604659, 181010596, 161141480, 90413332, 113121875, 63397548, 225058824, 212411389, 66698474, 121145343, 107166102,
  181071772, 147118977, 63677852, 160868988
]

theorem l99PeriodTail082_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk82.filter selectedCellPredicate) l99PeriodTail082Floors = true := by decide +kernel

theorem l99PeriodTail082_sum : l99PeriodTail082Floors.sum = 2466003687 := by decide +kernel

theorem l99PeriodTail082_lower : (2466003687 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk82.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail082_checked
  simpa only [l99PeriodTail082_sum, Nat.cast_ofNat] using h


def l99PeriodTail083Floors : List ℕ := [
  117047285, 94633149, 155608039, 112515433, 85146173, 61551095, 49508262, 456566671, 433016420, 47975306, 58906149, 79749460, 95904175, 129100668, 76518969, 100245082,
  123677943, 156414554, 119541335, 74628333
]

theorem l99PeriodTail083_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk83.filter selectedCellPredicate) l99PeriodTail083Floors = true := by decide +kernel

theorem l99PeriodTail083_sum : l99PeriodTail083Floors.sum = 2628254501 := by decide +kernel

theorem l99PeriodTail083_lower : (2628254501 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk83.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail083_checked
  simpa only [l99PeriodTail083_sum, Nat.cast_ofNat] using h


def l99PeriodTail084Floors : List ℕ := [
  82623731, 194989944, 179988148, 68176685, 151317719, 94067879, 67662409, 98403363, 63021991, 287533997, 271511502, 66283588, 104847902, 79193073, 111681728, 156297322,
  65736196, 193309074, 152139146, 58598526
]

theorem l99PeriodTail084_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk84.filter selectedCellPredicate) l99PeriodTail084Floors = true := by decide +kernel

theorem l99PeriodTail084_sum : l99PeriodTail084Floors.sum = 2547383923 := by decide +kernel

theorem l99PeriodTail084_lower : (2547383923 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk84.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail084_checked
  simpa only [l99PeriodTail084_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
