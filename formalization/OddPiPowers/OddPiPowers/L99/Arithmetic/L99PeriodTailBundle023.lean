module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail115Floors : List ℕ := [
  135261079, 112423732, 189676932, 185776901, 129610235, 88218797, 67738998, 97190075, 71904367, 48207720, 304075051, 332027264, 63188856, 83188878, 128248403, 94253985,
  140033201, 116615095, 65638104, 83387806
]

theorem l99PeriodTail115_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk115.filter selectedCellPredicate) l99PeriodTail115Floors = true := by decide +kernel

theorem l99PeriodTail115_sum : l99PeriodTail115Floors.sum = 2536665479 := by decide +kernel

theorem l99PeriodTail115_lower : (2536665479 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk115.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail115_checked
  simpa only [l99PeriodTail115_sum, Nat.cast_ofNat] using h


def l99PeriodTail116Floors : List ℕ := [
  216047558, 161290629, 51612517, 94460075, 91366958, 144190664, 184805354, 143222361, 105466080, 86094079, 143117749, 104667217, 79877052, 58118371, 46989118, 443777132,
  439089805, 49779534, 61416048, 83647659
]

theorem l99PeriodTail116_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk116.filter selectedCellPredicate) l99PeriodTail116Floors = true := by decide +kernel

theorem l99PeriodTail116_sum : l99PeriodTail116Floors.sum = 2789035960 := by decide +kernel

theorem l99PeriodTail116_lower : (2789035960 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk116.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail116_checked
  simpa only [l99PeriodTail116_sum, Nat.cast_ofNat] using h


def l99PeriodTail117Floors : List ℕ := [
  101368930, 137860489, 82505817, 109000765, 135876399, 174089582, 134836972, 84987404, 94792994, 226676126, 196631420, 81655743, 64495361, 113301872, 115281628, 83635005,
  122663678, 79187335, 55345704, 336326878
]

theorem l99PeriodTail117_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk117.filter selectedCellPredicate) l99PeriodTail117Floors = true := by decide +kernel

theorem l99PeriodTail117_sum : l99PeriodTail117Floors.sum = 2530520102 := by decide +kernel

theorem l99PeriodTail117_lower : (2530520102 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk117.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail117_checked
  simpa only [l99PeriodTail117_sum, Nat.cast_ofNat] using h


def l99PeriodTail118Floors : List ℕ := [
  301229270, 60914354, 88874534, 141819820, 116454783, 154011173, 144950043, 91986697, 110124072, 63626820, 237760655, 264173457, 87182650, 152495872, 141114006, 66679717,
  200464656, 203064953, 99615557, 93540750
]

theorem l99PeriodTail118_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk118.filter selectedCellPredicate) l99PeriodTail118Floors = true := by decide +kernel

theorem l99PeriodTail118_sum : l99PeriodTail118Floors.sum = 2820083839 := by decide +kernel

theorem l99PeriodTail118_lower : (2820083839 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk118.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail118_checked
  simpa only [l99PeriodTail118_sum, Nat.cast_ofNat] using h


def l99PeriodTail119Floors : List ℕ := [
  170952063, 152368442, 64742086, 66521591, 123259705, 163781654, 142782339, 115918490, 102745008, 84055054, 75477466, 129987767, 107954787, 99366584, 84964984, 79606311,
  64180771, 56539921, 46004658, 41110385
]

theorem l99PeriodTail119_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk119.filter selectedCellPredicate) l99PeriodTail119Floors = true := by decide +kernel

theorem l99PeriodTail119_sum : l99PeriodTail119Floors.sum = 1972320066 := by decide +kernel

theorem l99PeriodTail119_lower : (1972320066 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk119.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail119_checked
  simpa only [l99PeriodTail119_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
