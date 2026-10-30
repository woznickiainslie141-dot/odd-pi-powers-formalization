module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail125Floors : List ℕ := [
  54966851, 48023481, 767122128, 482955975, 35380388, 44412627, 55809413, 70398509, 83006713, 99335213, 121007335, 150640227, 90055832, 102621009, 118013169, 137149108,
  148938515, 51024801, 122099509, 138939325
]

theorem l99PeriodTail125_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk125.filter selectedCellPredicate) l99PeriodTail125Floors = true := by decide +kernel

theorem l99PeriodTail125_sum : l99PeriodTail125Floors.sum = 2921900128 := by decide +kernel

theorem l99PeriodTail125_lower : (2921900128 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk125.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail125_checked
  simpa only [l99PeriodTail125_sum, Nat.cast_ofNat] using h


def l99PeriodTail126Floors : List ℕ := [
  76912156, 82608809, 185041690, 159448553, 57770697, 123418294, 123906728, 72530146, 220450625, 221572300, 65152050, 104950099, 88511425, 152819061, 152053891, 108126051,
  155507261, 98559987, 68052892, 45980019
]

theorem l99PeriodTail126_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk126.filter selectedCellPredicate) l99PeriodTail126Floors = true := by decide +kernel

theorem l99PeriodTail126_sum : l99PeriodTail126Floors.sum = 2363372734 := by decide +kernel

theorem l99PeriodTail126_lower : (2363372734 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk126.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail126_checked
  simpa only [l99PeriodTail126_sum, Nat.cast_ofNat] using h


def l99PeriodTail127Floors : List ℕ := [
  321855581, 318563574, 48720806, 71415228, 95536732, 149534360, 103085953, 155668618, 142996290, 82185821, 104889349, 59775275, 218177448, 215280148, 69617155, 128864825,
  116673818, 203096397, 170783175, 69777087
]

theorem l99PeriodTail127_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk127.filter selectedCellPredicate) l99PeriodTail127Floors = true := by decide +kernel

theorem l99PeriodTail127_sum : l99PeriodTail127Floors.sum = 2846497640 := by decide +kernel

theorem l99PeriodTail127_lower : (2846497640 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk127.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail127_checked
  simpa only [l99PeriodTail127_sum, Nat.cast_ofNat] using h


def l99PeriodTail128Floors : List ℕ := [
  70021530, 135289461, 159124450, 131955399, 102643699, 87674138, 141871353, 118987641, 94844449, 77372596, 59373646, 50137519, 39325927, 551570910, 540403724, 51395860,
  55870118, 65897805, 73256239, 89280489
]

theorem l99PeriodTail128_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk128.filter selectedCellPredicate) l99PeriodTail128Floors = true := by decide +kernel

theorem l99PeriodTail128_sum : l99PeriodTail128Floors.sum = 2696296953 := by decide +kernel

theorem l99PeriodTail128_lower : (2696296953 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk128.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail128_checked
  simpa only [l99PeriodTail128_sum, Nat.cast_ofNat] using h


def l99PeriodTail129Floors : List ℕ := [
  102653706, 131395475, 80532006, 101444628, 119421153, 153612857, 173360996, 66392967, 148810603, 174850304, 91775672, 108956554, 58492093, 194085534, 210117717, 78348047,
  71614585, 114195423, 113700897, 80901912
]

theorem l99PeriodTail129_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk129.filter selectedCellPredicate) l99PeriodTail129Floors = true := by decide +kernel

theorem l99PeriodTail129_sum : l99PeriodTail129Floors.sum = 2374663129 := by decide +kernel

theorem l99PeriodTail129_lower : (2374663129 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk129.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail129_checked
  simpa only [l99PeriodTail129_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
