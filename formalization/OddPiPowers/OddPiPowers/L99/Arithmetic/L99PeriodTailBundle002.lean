module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail010Floors : List ℕ := [
  72857615, 102576318, 172513039, 139426809, 211541500, 214476346, 134313216, 156606310, 102748849, 68901719, 49414141, 323088167, 282636144, 51645660, 72602976, 109563731,
  84805933, 113763259, 149133582, 59411438
]

theorem l99PeriodTail010_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk10.filter selectedCellPredicate) l99PeriodTail010Floors = true := by decide +kernel

theorem l99PeriodTail010_sum : l99PeriodTail010Floors.sum = 2672026752 := by decide +kernel

theorem l99PeriodTail010_lower : (2672026752 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk10.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail010_checked
  simpa only [l99PeriodTail010_sum, Nat.cast_ofNat] using h


def l99PeriodTail011Floors : List ℕ := [
  162096477, 163818875, 60937831, 155136256, 103166486, 77860918, 118854951, 79737529, 57202711, 320871806, 327993513, 55374652, 77870177, 107770438, 84542397, 122919192,
  160288419, 69214798, 174419540, 176421809
]

theorem l99PeriodTail011_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk11.filter selectedCellPredicate) l99PeriodTail011Floors = true := by decide +kernel

theorem l99PeriodTail011_sum : l99PeriodTail011Floors.sum = 2656498775 := by decide +kernel

theorem l99PeriodTail011_lower : (2656498775 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk11.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail011_checked
  simpa only [l99PeriodTail011_sum, Nat.cast_ofNat] using h


def l99PeriodTail012Floors : List ℕ := [
  71137100, 62514076, 130940743, 140683863, 98641906, 139067658, 100526417, 72142047, 54292225, 384563967, 308510134, 48657999, 70530924, 99220828, 149885362, 107843287,
  144816736, 117864508, 71124579, 81661039
]

theorem l99PeriodTail012_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk12.filter selectedCellPredicate) l99PeriodTail012Floors = true := by decide +kernel

theorem l99PeriodTail012_sum : l99PeriodTail012Floors.sum = 2454625398 := by decide +kernel

theorem l99PeriodTail012_lower : (2454625398 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk12.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail012_checked
  simpa only [l99PeriodTail012_sum, Nat.cast_ofNat] using h


def l99PeriodTail013Floors : List ℕ := [
  205925397, 191121242, 77118167, 67795748, 123989074, 130919512, 98915941, 139540635, 93720338, 67285909, 46048335, 326518537, 444784496, 56236190, 77349098, 97057700,
  136598673, 85432204, 114949525, 148666759
]

theorem l99PeriodTail013_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk13.filter selectedCellPredicate) l99PeriodTail013Floors = true := by decide +kernel

theorem l99PeriodTail013_sum : l99PeriodTail013Floors.sum = 2729973480 := by decide +kernel

theorem l99PeriodTail013_lower : (2729973480 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk13.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail013_checked
  simpa only [l99PeriodTail013_sum, Nat.cast_ofNat] using h


def l99PeriodTail014Floors : List ℕ := [
  199768661, 164513327, 99327874, 122241394, 63650908, 224291395, 226673860, 65206876, 117873205, 96265745, 173897704, 200462756, 140741263, 101671647, 74924127, 123272038,
  95925642, 72239836, 56362673, 456528738
]

theorem l99PeriodTail014_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk14.filter selectedCellPredicate) l99PeriodTail014Floors = true := by decide +kernel

theorem l99PeriodTail014_sum : l99PeriodTail014Floors.sum = 2875839669 := by decide +kernel

theorem l99PeriodTail014_lower : (2875839669 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk14.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail014_checked
  simpa only [l99PeriodTail014_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
