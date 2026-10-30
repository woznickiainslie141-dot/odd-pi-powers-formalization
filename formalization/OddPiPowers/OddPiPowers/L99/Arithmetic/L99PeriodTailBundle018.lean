module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail090Floors : List ℕ := [
  38779787, 713523929, 706197962, 37966361, 46124255, 51681186, 63165608, 71818062, 88715908, 95454452, 111911233, 122792603, 148372736, 79212882, 96461471, 108369380,
  132846285, 151555389, 174516160, 141953388
]

theorem l99PeriodTail090_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk90.filter selectedCellPredicate) l99PeriodTail090Floors = true := by decide +kernel

theorem l99PeriodTail090_sum : l99PeriodTail090Floors.sum = 3181419037 := by decide +kernel

theorem l99PeriodTail090_lower : (3181419037 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk90.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail090_checked
  simpa only [l99PeriodTail090_sum, Nat.cast_ofNat] using h


def l99PeriodTail091Floors : List ℕ := [
  71308586, 81107671, 176697245, 184842673, 101481146, 116670739, 56960392, 183262195, 204323801, 73428089, 155809464, 156010676, 89992284, 55889634, 257471579, 246648691,
  71784886, 124523872, 104287835, 164840373
]

theorem l99PeriodTail091_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk91.filter selectedCellPredicate) l99PeriodTail091Floors = true := by decide +kernel

theorem l99PeriodTail091_sum : l99PeriodTail091Floors.sum = 2677341831 := by decide +kernel

theorem l99PeriodTail091_lower : (2677341831 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk91.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail091_checked
  simpa only [l99PeriodTail091_sum, Nat.cast_ofNat] using h


def l99PeriodTail092Floors : List ℕ := [
  175827450, 123877017, 150456273, 102452522, 64946305, 47356462, 302348435, 293179160, 51703357, 65109524, 93323088, 133797519, 99108321, 148418124, 124685272, 77077526,
  97782985, 51178742, 200651208, 211552845
]

theorem l99PeriodTail092_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk92.filter selectedCellPredicate) l99PeriodTail092Floors = true := by decide +kernel

theorem l99PeriodTail092_sum : l99PeriodTail092Floors.sum = 2614832135 := by decide +kernel

theorem l99PeriodTail092_lower : (2614832135 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk92.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail092_checked
  simpa only [l99PeriodTail092_sum, Nat.cast_ofNat] using h


def l99PeriodTail093Floors : List ℕ := [
  62571315, 115130441, 95511509, 178396019, 148348528, 65182914, 167360055, 124341125, 93715490, 78414395, 66577825, 116683922, 97094853, 76918789, 62439627, 51697101,
  591520605, 396891669, 45358078, 54101599
]

theorem l99PeriodTail093_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk93.filter selectedCellPredicate) l99PeriodTail093Floors = true := by decide +kernel

theorem l99PeriodTail093_sum : l99PeriodTail093Floors.sum = 2688255859 := by decide +kernel

theorem l99PeriodTail093_lower : (2688255859 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk93.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail093_checked
  simpa only [l99PeriodTail093_sum, Nat.cast_ofNat] using h


def l99PeriodTail094Floors : List ℕ := [
  65642975, 81318454, 103370190, 135798817, 85234710, 101091614, 121827321, 149672019, 111095614, 67941051, 68351734, 170033906, 207298634, 121673761, 126136292, 74830253,
  236303087, 228150334, 69059380, 113182836
]

theorem l99PeriodTail094_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk94.filter selectedCellPredicate) l99PeriodTail094Floors = true := by decide +kernel

theorem l99PeriodTail094_sum : l99PeriodTail094Floors.sum = 2438012982 := by decide +kernel

theorem l99PeriodTail094_lower : (2438012982 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk94.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail094_checked
  simpa only [l99PeriodTail094_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
