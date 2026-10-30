module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail005Floors : List ℕ := [
  179758074, 84922486, 92530324, 188363433, 179121160, 91188016, 99399375, 188015331, 192712921, 90621618, 99415373, 202652085, 191919254, 97840019, 107387131, 202215715,
  155234018, 65554344, 123615957, 125308223
]

theorem l99PeriodTail005_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk5.filter selectedCellPredicate) l99PeriodTail005Floors = true := by decide +kernel

theorem l99PeriodTail005_sum : l99PeriodTail005Floors.sum = 2757774857 := by decide +kernel

theorem l99PeriodTail005_lower : (2757774857 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk5.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail005_checked
  simpa only [l99PeriodTail005_sum, Nat.cast_ofNat] using h


def l99PeriodTail006Floors : List ℕ := [
  63299608, 192534568, 168501619, 61704244, 124720460, 126500971, 59012432, 179601287, 168250334, 62081045, 115078973, 116795351, 59053362, 179842397, 167248812, 56606663,
  125981669, 116316973, 58842194, 179326478
]

theorem l99PeriodTail006_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk6.filter selectedCellPredicate) l99PeriodTail006Floors = true := by decide +kernel

theorem l99PeriodTail006_sum : l99PeriodTail006Floors.sum = 2381299440 := by decide +kernel

theorem l99PeriodTail006_lower : (2381299440 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk6.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail006_checked
  simpa only [l99PeriodTail006_sum, Nat.cast_ofNat] using h


def l99PeriodTail007Floors : List ℕ := [
  183644299, 62201344, 125918622, 115183128, 64780016, 197576486, 145485553, 69570453, 116736228, 94103117, 142360145, 135366190, 91021456, 114662663, 69274965, 263196442,
  268791648, 68093127, 114298490, 86030535
]

theorem l99PeriodTail007_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk7.filter selectedCellPredicate) l99PeriodTail007Floors = true := by decide +kernel

theorem l99PeriodTail007_sum : l99PeriodTail007Floors.sum = 2528294907 := by decide +kernel

theorem l99PeriodTail007_lower : (2528294907 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk7.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail007_checked
  simpa only [l99PeriodTail007_sum, Nat.cast_ofNat] using h


def l99PeriodTail008Floors : List ℕ := [
  139507910, 131621462, 82220039, 111589738, 67443920, 273519270, 239708830, 65834707, 110551880, 89194588, 135064938, 126107073, 84879022, 107020529, 64709628, 240754633,
  246481483, 62539208, 105065077, 77100767
]

theorem l99PeriodTail008_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk8.filter selectedCellPredicate) l99PeriodTail008Floors = true := by decide +kernel

theorem l99PeriodTail008_sum : l99PeriodTail008Floors.sum = 2560914702 := by decide +kernel

theorem l99PeriodTail008_lower : (2560914702 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk8.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail008_checked
  simpa only [l99PeriodTail008_sum, Nat.cast_ofNat] using h


def l99PeriodTail009Floors : List ℕ := [
  128500046, 189186336, 119446836, 150685435, 97231636, 65154893, 329842616, 294682261, 63944716, 96424062, 162073106, 139630864, 198465100, 201039919, 135481919, 159615335,
  103509007, 64759112, 328108278, 335473628
]

theorem l99PeriodTail009_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk9.filter selectedCellPredicate) l99PeriodTail009Floors = true := by decide +kernel

theorem l99PeriodTail009_sum : l99PeriodTail009Floors.sum = 3363255105 := by decide +kernel

theorem l99PeriodTail009_lower : (3363255105 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk9.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail009_checked
  simpa only [l99PeriodTail009_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
