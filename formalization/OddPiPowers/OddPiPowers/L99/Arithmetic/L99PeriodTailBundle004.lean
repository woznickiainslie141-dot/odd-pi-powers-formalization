module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail020Floors : List ℕ := [
  307157602, 60199976, 81344448, 128272986, 96564290, 145404493, 125814114, 73264105, 93510310, 250774599, 198542343, 64436712, 120028387, 109525015, 192610900, 163922104,
  67910016, 190958863, 145893538, 122142181
]

theorem l99PeriodTail020_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk20.filter selectedCellPredicate) l99PeriodTail020Floors = true := by decide +kernel

theorem l99PeriodTail020_sum : l99PeriodTail020Floors.sum = 2738276982 := by decide +kernel

theorem l99PeriodTail020_lower : (2738276982 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk20.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail020_checked
  simpa only [l99PeriodTail020_sum, Nat.cast_ofNat] using h


def l99PeriodTail021Floors : List ℕ := [
  95773194, 82364342, 134382725, 113734256, 91307070, 74918148, 57764640, 48974153, 38544328, 552622008, 563990303, 47520213, 55535453, 70824239, 79108626, 96971214,
  112295800, 145047202, 89635044, 113682558
]

theorem l99PeriodTail021_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk21.filter selectedCellPredicate) l99PeriodTail021Floors = true := by decide +kernel

theorem l99PeriodTail021_sum : l99PeriodTail021Floors.sum = 2664995516 := by decide +kernel

theorem l99PeriodTail021_lower : (2664995516 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk21.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail021_checked
  simpa only [l99PeriodTail021_sum, Nat.cast_ofNat] using h


def l99PeriodTail022Floors : List ℕ := [
  134902025, 162674129, 118546634, 71580892, 77274389, 174581206, 207607062, 110088136, 121588719, 71159132, 238380283, 205843378, 61094406, 107202704, 90996958, 146145310,
  171330972, 122910071, 152817627, 105142750
]

theorem l99PeriodTail022_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk22.filter selectedCellPredicate) l99PeriodTail022Floors = true := by decide +kernel

theorem l99PeriodTail022_sum : l99PeriodTail022Floors.sum = 2651866783 := by decide +kernel

theorem l99PeriodTail022_lower : (2651866783 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk22.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail022_checked
  simpa only [l99PeriodTail022_sum, Nat.cast_ofNat] using h


def l99PeriodTail023Floors : List ℕ := [
  67768051, 49788549, 300494645, 303584965, 50897933, 69536295, 100707084, 146669381, 110477064, 168303057, 144124285, 90430049, 116158604, 61442153, 226363141, 245682041,
  74093606, 138082331, 126073798, 59012816
]

theorem l99PeriodTail023_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk23.filter selectedCellPredicate) l99PeriodTail023Floors = true := by decide +kernel

theorem l99PeriodTail023_sum : l99PeriodTail023Floors.sum = 2649689848 := by decide +kernel

theorem l99PeriodTail023_lower : (2649689848 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk23.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail023_checked
  simpa only [l99PeriodTail023_sum, Nat.cast_ofNat] using h


def l99PeriodTail024Floors : List ℕ := [
  162873884, 189011394, 84379135, 78559356, 141912386, 124709513, 71065550, 190146726, 150847985, 120526846, 96743126, 77821694, 130173252, 114070139, 101442103, 91286556,
  77419782, 66489592, 57721480, 50580485
]

theorem l99PeriodTail024_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk24.filter selectedCellPredicate) l99PeriodTail024Floors = true := by decide +kernel

theorem l99PeriodTail024_sum : l99PeriodTail024Floors.sum = 2177780984 := by decide +kernel

theorem l99PeriodTail024_lower : (2177780984 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk24.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail024_checked
  simpa only [l99PeriodTail024_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
