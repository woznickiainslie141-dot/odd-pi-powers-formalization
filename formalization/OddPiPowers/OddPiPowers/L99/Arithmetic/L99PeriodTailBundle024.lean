module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail120Floors : List ℕ := [
  33597901, 631619743, 716448153, 39363944, 47935617, 53853368, 66017304, 75315110, 86725956, 93177789, 109815760, 120401376, 69509479, 84070199, 93732752, 113926273,
  128720704, 157873738, 168475177, 61888298
]

theorem l99PeriodTail120_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk120.filter selectedCellPredicate) l99PeriodTail120Floors = true := by decide +kernel

theorem l99PeriodTail120_sum : l99PeriodTail120Floors.sum = 2952468641 := by decide +kernel

theorem l99PeriodTail120_lower : (2952468641 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk120.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail120_checked
  simpa only [l99PeriodTail120_sum, Nat.cast_ofNat] using h


def l99PeriodTail121Floors : List ℕ := [
  133757583, 148955705, 74778727, 85889880, 188295080, 145718281, 56224175, 118428859, 127135674, 61974062, 200675742, 226073756, 81853251, 68067019, 115590457, 112625580,
  78624785, 111099409, 69273273, 298736808
]

theorem l99PeriodTail121_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk121.filter selectedCellPredicate) l99PeriodTail121Floors = true := by decide +kernel

theorem l99PeriodTail121_sum : l99PeriodTail121Floors.sum = 2503778106 := by decide +kernel

theorem l99PeriodTail121_lower : (2503778106 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk121.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail121_checked
  simpa only [l99PeriodTail121_sum, Nat.cast_ofNat] using h


def l99PeriodTail122Floors : List ℕ := [
  236105470, 54947474, 91811422, 160134666, 134969131, 55228830, 155116741, 163545015, 62707832, 164469086, 113425715, 87962069, 138172522, 95357653, 69773454, 49170144,
  366534791, 392843294, 52062687, 73198913
]

theorem l99PeriodTail122_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk122.filter selectedCellPredicate) l99PeriodTail122Floors = true := by decide +kernel

theorem l99PeriodTail122_sum : l99PeriodTail122Floors.sum = 2717536909 := by decide +kernel

theorem l99PeriodTail122_lower : (2717536909 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk122.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail122_checked
  simpa only [l99PeriodTail122_sum, Nat.cast_ofNat] using h


def l99PeriodTail123Floors : List ℕ := [
  92483777, 133175494, 84255513, 117020618, 155443687, 63813191, 164440330, 198709482, 123639938, 145574564, 82921499, 53553189, 229718730, 262530580, 64949594, 96284351,
  73453566, 112722209, 161157899, 74956488
]

theorem l99PeriodTail123_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk123.filter selectedCellPredicate) l99PeriodTail123Floors = true := by decide +kernel

theorem l99PeriodTail123_sum : l99PeriodTail123Floors.sum = 2490804699 := by decide +kernel

theorem l99PeriodTail123_lower : (2490804699 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk123.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail123_checked
  simpa only [l99PeriodTail123_sum, Nat.cast_ofNat] using h


def l99PeriodTail124Floors : List ℕ := [
  205313409, 180170347, 55251744, 104127656, 88997317, 172878074, 150569371, 68226178, 64090935, 117194044, 152659095, 120292925, 95231018, 75521091, 125392263, 109876402,
  97735335, 87984095, 74271829, 63533400
]

theorem l99PeriodTail124_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk124.filter selectedCellPredicate) l99PeriodTail124Floors = true := by decide +kernel

theorem l99PeriodTail124_sum : l99PeriodTail124Floors.sum = 2209316528 := by decide +kernel

theorem l99PeriodTail124_lower : (2209316528 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk124.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail124_checked
  simpa only [l99PeriodTail124_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
