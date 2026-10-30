module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail000Floors : List ℕ := [
  52851017, 53940550, 58505634, 59737126, 64596615, 65985552, 71165317, 72729117, 78257931, 80016223, 85926168, 87901122, 89944958, 87677062, 89764216, 87330456,
  89460056, 86843855, 89014521
]

theorem l99PeriodTail000_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk0.filter selectedCellPredicate) l99PeriodTail000Floors = true := by decide +kernel

theorem l99PeriodTail000_sum : l99PeriodTail000Floors.sum = 1451647496 := by decide +kernel

theorem l99PeriodTail000_lower : (1451647496 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk0.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail000_checked
  simpa only [l99PeriodTail000_sum, Nat.cast_ofNat] using h


def l99PeriodTail001Floors : List ℕ := [
  86197178, 88406913, 85367269, 87613307, 84327345, 86605974, 83046343, 85352678, 81488125, 83815829, 79610506, 81951446, 77364080, 79707883, 74690759, 77024267,
  71521980, 73828550, 67776470, 70035089
]

theorem l99PeriodTail001_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk1.filter selectedCellPredicate) l99PeriodTail001Floors = true := by decide +kernel

theorem l99PeriodTail001_sum : l99PeriodTail001Floors.sum = 1605731991 := by decide +kernel

theorem l99PeriodTail001_lower : (1605731991 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk1.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail001_checked
  simpa only [l99PeriodTail001_sum, Nat.cast_ofNat] using h


def l99PeriodTail002Floors : List ℕ := [
  63357456, 65541599, 58149141, 60225308, 52012240, 53938053, 44778274, 46499990, 36242214, 37691443, 12944414, 118876503, 121326764, 130734324, 126460143, 136324870,
  139255588, 149770358, 145407824, 156461021
]

theorem l99PeriodTail002_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk2.filter selectedCellPredicate) l99PeriodTail002Floors = true := by decide +kernel

theorem l99PeriodTail002_sum : l99PeriodTail002Floors.sum = 1755997527 := by decide +kernel

theorem l99PeriodTail002_lower : (1755997527 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk2.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail002_checked
  simpa only [l99PeriodTail002_sum, Nat.cast_ofNat] using h


def l99PeriodTail003Floors : List ℕ := [
  159975747, 171790761, 175738535, 179823971, 175289090, 179461064, 174594587, 178851345, 173620135, 177958919, 172325599, 176742408, 170664687, 175153989, 168583864, 173138232,
  166021040, 170630705, 162903981, 167556273
]

theorem l99PeriodTail003_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk3.filter selectedCellPredicate) l99PeriodTail003Floors = true := by decide +kernel

theorem l99PeriodTail003_sum : l99PeriodTail003Floors.sum = 3450824932 := by decide +kernel

theorem l99PeriodTail003_lower : (3450824932 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk3.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail003_checked
  simpa only [l99PeriodTail003_sum, Nat.cast_ofNat] using h


def l99PeriodTail004Floors : List ℕ := [
  159148380, 163827032, 154655488, 159339767, 158450991, 75416020, 81272665, 165083843, 158022706, 80264870, 86526208, 164852022, 168433910, 79890387, 86536976, 175956995,
  167915041, 85379764, 92517284, 175674871
]

theorem l99PeriodTail004_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk4.filter selectedCellPredicate) l99PeriodTail004Floors = true := by decide +kernel

theorem l99PeriodTail004_sum : l99PeriodTail004Floors.sum = 2639165220 := by decide +kernel

theorem l99PeriodTail004_lower : (2639165220 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk4.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail004_checked
  simpa only [l99PeriodTail004_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
