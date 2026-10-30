module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail145Floors : List ℕ := [
  169905919, 83461751, 88836186, 162135471, 158448640, 71890001, 77005314, 151442468, 136719114, 67238343, 72049385, 130867792, 128082003, 57771982, 62360248, 122770801,
  110218386, 54260958, 58589469, 105785783
]

theorem l99PeriodTail145_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk145.filter selectedCellPredicate) l99PeriodTail145Floors = true := by decide +kernel

theorem l99PeriodTail145_sum : l99PeriodTail145Floors.sum = 2069840014 := by decide +kernel

theorem l99PeriodTail145_lower : (2069840014 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk145.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail145_checked
  simpa only [l99PeriodTail145_sum, Nat.cast_ofNat] using h


def l99PeriodTail146Floors : List ℕ := [
  154729630, 163829126, 159078337, 167408846, 162691059, 170336849, 153834681, 149675258, 134475950, 130935676, 116905607, 113906845, 100929094, 98404896, 86376800, 84269258,
  73100373, 71359251, 60969651, 59551245
]

theorem l99PeriodTail146_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk146.filter selectedCellPredicate) l99PeriodTail146Floors = true := by decide +kernel

theorem l99PeriodTail146_sum : l99PeriodTail146Floors.sum = 2412768432 := by decide +kernel

theorem l99PeriodTail146_lower : (2412768432 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk146.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail146_checked
  simpa only [l99PeriodTail146_sum, Nat.cast_ofNat] using h


def l99PeriodTail147Floors : List ℕ := [
  49870085, 48736278, 39700585, 38818048, 37964615, 37139022, 29072055, 28453298, 27854087, 27273608, 20033315, 19624343, 19227769, 18843095, 36577439, 46893597,
  45123514, 54314745, 52339111, 60563212
]

theorem l99PeriodTail147_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk147.filter selectedCellPredicate) l99PeriodTail147Floors = true := by decide +kernel

theorem l99PeriodTail147_sum : l99PeriodTail147Floors.sum = 738421821 := by decide +kernel

theorem l99PeriodTail147_lower : (738421821 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk147.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail147_checked
  simpa only [l99PeriodTail147_sum, Nat.cast_ofNat] using h


def l99PeriodTail148Floors : List ℕ := [
  58437614, 65825654, 63593694, 70255269, 67951237, 73978557, 71629458, 77100555, 74727669, 79708932, 77329015, 81877219, 79503437, 83667362, 81310024, 85131771,
  76884695, 74806298, 67210204, 65441156
]

theorem l99PeriodTail148_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk148.filter selectedCellPredicate) l99PeriodTail148Floors = true := by decide +kernel

theorem l99PeriodTail148_sum : l99PeriodTail148Floors.sum = 1476369820 := by decide +kernel

theorem l99PeriodTail148_lower : (1476369820 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk148.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail148_checked
  simpa only [l99PeriodTail148_sum, Nat.cast_ofNat] using h


def l99PeriodTail149Floors : List ℕ := [
  58429292, 56930810, 50444766, 49183404, 43171892, 42118721, 36536555, 35666478, 30473725, 29764907, 24926173, 24359570, 19843391, 19402351, 15180683, 14850613,
  10898394, 10666475, 6961254, 6816205
]

theorem l99PeriodTail149_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk149.filter selectedCellPredicate) l99PeriodTail149Floors = true := by decide +kernel

theorem l99PeriodTail149_sum : l99PeriodTail149Floors.sum = 586625659 := by decide +kernel

theorem l99PeriodTail149_lower : (586625659 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk149.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail149_checked
  simpa only [l99PeriodTail149_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
