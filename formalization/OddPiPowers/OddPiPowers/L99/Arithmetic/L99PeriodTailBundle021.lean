module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail105Floors : List ℕ := [
  52819109, 438390412, 323306705, 40877130, 56175657, 79022798, 106749341, 152173092, 103259308, 131166059, 172153465, 64611524, 165914524, 154061610, 58586335, 130486807,
  140193650, 85673122, 50779263, 232984480
]

theorem l99PeriodTail105_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk105.filter selectedCellPredicate) l99PeriodTail105Floors = true := by decide +kernel

theorem l99PeriodTail105_sum : l99PeriodTail105Floors.sum = 2739384391 := by decide +kernel

theorem l99PeriodTail105_lower : (2739384391 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk105.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail105_checked
  simpa only [l99PeriodTail105_sum, Nat.cast_ofNat] using h


def l99PeriodTail106Floors : List ℕ := [
  260625192, 59074324, 93703556, 65526551, 108144741, 152946087, 70457710, 205499611, 198435980, 93804997, 86169116, 152879299, 190542722, 155440699, 119280356, 100724720,
  86186467, 80799277, 132838409, 112710358
]

theorem l99PeriodTail106_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk106.filter selectedCellPredicate) l99PeriodTail106Floors = true := by decide +kernel

theorem l99PeriodTail106_sum : l99PeriodTail106Floors.sum = 2525790172 := by decide +kernel

theorem l99PeriodTail106_lower : (2525790172 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk106.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail106_checked
  simpa only [l99PeriodTail106_sum, Nat.cast_ofNat] using h


def l99PeriodTail107Floors : List ℕ := [
  84587301, 69784113, 54050030, 45999836, 571697688, 565653283, 48743515, 57168090, 73212839, 82188357, 101364932, 118282574, 71685846, 103242546, 112229893, 132372576,
  147153111, 179340625, 132062521, 80318043
]

theorem l99PeriodTail107_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk107.filter selectedCellPredicate) l99PeriodTail107Floors = true := by decide +kernel

theorem l99PeriodTail107_sum : l99PeriodTail107Floors.sum = 2831137719 := by decide +kernel

theorem l99PeriodTail107_lower : (2831137719 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk107.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail107_checked
  simpa only [l99PeriodTail107_sum, Nat.cast_ofNat] using h


def l99PeriodTail108Floors : List ℕ := [
  87173905, 198754341, 175243268, 64427084, 139341217, 143381031, 84545637, 53167596, 251293677, 251721347, 75515403, 133355927, 114053337, 184842961, 143345811, 55611990,
  147602324, 103308129, 81025367, 128833628
]

theorem l99PeriodTail108_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk108.filter selectedCellPredicate) l99PeriodTail108Floors = true := by decide +kernel

theorem l99PeriodTail108_sum : l99PeriodTail108Floors.sum = 2616543980 := by decide +kernel

theorem l99PeriodTail108_lower : (2616543980 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk108.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail108_checked
  simpa only [l99PeriodTail108_sum, Nat.cast_ofNat] using h


def l99PeriodTail109Floors : List ℕ := [
  90006305, 66432830, 47121375, 359829919, 371552295, 50456840, 71840584, 91041193, 132767181, 92155188, 129514269, 161297954, 67055821, 176019864, 155489454, 60338654,
  148269998, 94534449, 74979942, 102436694
]

theorem l99PeriodTail109_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk109.filter selectedCellPredicate) l99PeriodTail109Floors = true := by decide +kernel

theorem l99PeriodTail109_sum : l99PeriodTail109Floors.sum = 2543140809 := by decide +kernel

theorem l99PeriodTail109_lower : (2543140809 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk109.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail109_checked
  simpa only [l99PeriodTail109_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
