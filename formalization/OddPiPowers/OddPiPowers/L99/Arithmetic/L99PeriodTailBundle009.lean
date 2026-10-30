module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail045Floors : List ℕ := [
  48920066, 425596889, 375597063, 49365601, 68130977, 89759319, 123629755, 81131394, 99998471, 126312770, 151926964, 140545034, 82820476, 93303456, 227170860, 218856015,
  78753012, 73640529, 129971425, 134884999
]

theorem l99PeriodTail045_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk45.filter selectedCellPredicate) l99PeriodTail045Floors = true := by decide +kernel

theorem l99PeriodTail045_sum : l99PeriodTail045Floors.sum = 2820315075 := by decide +kernel

theorem l99PeriodTail045_lower : (2820315075 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk45.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail045_checked
  simpa only [l99PeriodTail045_sum, Nat.cast_ofNat] using h


def l99PeriodTail046Floors : List ℕ := [
  99098300, 135859357, 88760687, 62535579, 333024343, 311759180, 50034677, 74929013, 101860821, 71407076, 101301016, 138395900, 200432856, 192304324, 114395041, 138772863,
  87858646, 57627394, 277328301, 220435931
]

theorem l99PeriodTail046_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk46.filter selectedCellPredicate) l99PeriodTail046Floors = true := by decide +kernel

theorem l99PeriodTail046_sum : l99PeriodTail046Floors.sum = 2858121305 := by decide +kernel

theorem l99PeriodTail046_lower : (2858121305 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk46.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail046_checked
  simpa only [l99PeriodTail046_sum, Nat.cast_ofNat] using h


def l99PeriodTail047Floors : List ℕ := [
  50219201, 74204140, 120762705, 101318865, 147634761, 132467069, 92462001, 112726827, 66165328, 236053328, 221597222, 53294976, 87047996, 154823078, 147448712, 71121679,
  220636344, 190232811, 65707754, 127220463
]

theorem l99PeriodTail047_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk47.filter selectedCellPredicate) l99PeriodTail047Floors = true := by decide +kernel

theorem l99PeriodTail047_sum : l99PeriodTail047Floors.sum = 2473145260 := by decide +kernel

theorem l99PeriodTail047_lower : (2473145260 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk47.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail047_checked
  simpa only [l99PeriodTail047_sum, Nat.cast_ofNat] using h


def l99PeriodTail048Floors : List ℕ := [
  131296796, 59073483, 170130147, 211569031, 99795530, 96098682, 195891395, 169352118, 80369732, 83666449, 147860865, 138618049, 61024275, 64105991, 122554701, 170884223,
  169105769, 144789268, 133928652, 114688469
]

theorem l99PeriodTail048_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk48.filter selectedCellPredicate) l99PeriodTail048Floors = true := by decide +kernel

theorem l99PeriodTail048_sum : l99PeriodTail048Floors.sum = 2564803625 := by decide +kernel

theorem l99PeriodTail048_lower : (2564803625 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk48.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail048_checked
  simpa only [l99PeriodTail048_sum, Nat.cast_ofNat] using h


def l99PeriodTail049Floors : List ℕ := [
  106685974, 91201747, 85253130, 72607389, 68161564, 124524747, 110938936, 109407605, 98645278, 97523484, 88789355, 87943126, 80714405, 74341776, 63410946, 58770824,
  50070203, 46656123, 39617925, 37088981
]

theorem l99PeriodTail049_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk49.filter selectedCellPredicate) l99PeriodTail049Floors = true := by decide +kernel

theorem l99PeriodTail049_sum : l99PeriodTail049Floors.sum = 1592353518 := by decide +kernel

theorem l99PeriodTail049_lower : (1592353518 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk49.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail049_checked
  simpa only [l99PeriodTail049_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
