module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail135Floors : List ℕ := [
  74334557, 57629873, 45987293, 409279814, 376746592, 50739315, 70451084, 93549216, 130234073, 92992459, 115672694, 147802621, 181515763, 157457425, 93867951, 106725759,
  59039409, 189443232, 187446179, 57626462
]

theorem l99PeriodTail135_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk135.filter selectedCellPredicate) l99PeriodTail135Floors = true := by decide +kernel

theorem l99PeriodTail135_sum : l99PeriodTail135Floors.sum = 2698541771 := by decide +kernel

theorem l99PeriodTail135_lower : (2698541771 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk135.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail135_checked
  simpa only [l99PeriodTail135_sum, Nat.cast_ofNat] using h


def l99PeriodTail136Floors : List ℕ := [
  95346538, 83006964, 148935620, 155807687, 115948607, 82179373, 65438695, 97653952, 75692925, 51839220, 40201678, 289048730, 318268810, 49371582, 65582807, 91346836,
  123639907, 96406818, 139195607, 110768943
]

theorem l99PeriodTail136_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk136.filter selectedCellPredicate) l99PeriodTail136Floors = true := by decide +kernel

theorem l99PeriodTail136_sum : l99PeriodTail136Floors.sum = 2295681299 := by decide +kernel

theorem l99PeriodTail136_lower : (2295681299 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk136.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail136_checked
  simpa only [l99PeriodTail136_sum, Nat.cast_ofNat] using h


def l99PeriodTail137Floors : List ℕ := [
  72078738, 81989044, 203187850, 200676016, 79577500, 69309010, 124425230, 130259993, 88917779, 134813957, 96679068, 68723242, 51361346, 382570262, 294385288, 45337797,
  65263372, 90940223, 135481206, 96096287
]

theorem l99PeriodTail137_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk137.filter selectedCellPredicate) l99PeriodTail137Floors = true := by decide +kernel

theorem l99PeriodTail137_sum : l99PeriodTail137Floors.sum = 2512073208 := by decide +kernel

theorem l99PeriodTail137_lower : (2512073208 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk137.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail137_checked
  simpa only [l99PeriodTail137_sum, Nat.cast_ofNat] using h


def l99PeriodTail138Floors : List ℕ := [
  127261568, 102045648, 60897800, 69297124, 171855160, 169899866, 67419921, 156128905, 101307248, 82345344, 124053111, 75844064, 53933268, 319445976, 312493353, 51422185,
  77652299, 106841564, 75822474, 108836052
]

theorem l99PeriodTail138_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk138.filter selectedCellPredicate) l99PeriodTail138Floors = true := by decide +kernel

theorem l99PeriodTail138_sum : l99PeriodTail138Floors.sum = 2414802930 := by decide +kernel

theorem l99PeriodTail138_lower : (2414802930 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk138.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail138_checked
  simpa only [l99PeriodTail138_sum, Nat.cast_ofNat] using h


def l99PeriodTail139Floors : List ℕ := [
  151069443, 64284342, 159519046, 157837991, 67491244, 145210848, 94944657, 70776443, 106676792, 70688963, 50283670, 321037637, 269609966, 48106253, 67077439, 100027124,
  177863967, 140807387, 193867874, 191209346
]

theorem l99PeriodTail139_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk139.filter selectedCellPredicate) l99PeriodTail139Floors = true := by decide +kernel

theorem l99PeriodTail139_sum : l99PeriodTail139Floors.sum = 2648390432 := by decide +kernel

theorem l99PeriodTail139_lower : (2648390432 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk139.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail139_checked
  simpa only [l99PeriodTail139_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
