module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail095Floors : List ℕ := [
  105540884, 172381620, 191802242, 140341329, 98899657, 77978007, 115109475, 87627675, 59951256, 46212224, 327331144, 376697369, 56111220, 74001388, 102070196, 138319659,
  104710855, 147220320, 116972895, 69032695
]

theorem l99PeriodTail095_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk95.filter selectedCellPredicate) l99PeriodTail095Floors = true := by decide +kernel

theorem l99PeriodTail095_sum : l99PeriodTail095Floors.sum = 2608312110 := by decide +kernel

theorem l99PeriodTail095_lower : (2608312110 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk95.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail095_checked
  simpa only [l99PeriodTail095_sum, Nat.cast_ofNat] using h


def l99PeriodTail096Floors : List ℕ := [
  83851409, 189981398, 183574920, 77224276, 163640452, 105079046, 77321735, 115020019, 75259467, 53077470, 330708936, 309522961, 64306303, 94823974, 153824103, 128600594,
  173342187, 166757413, 107696371, 120822760
]

theorem l99PeriodTail096_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk96.filter selectedCellPredicate) l99PeriodTail096Floors = true := by decide +kernel

theorem l99PeriodTail096_sum : l99PeriodTail096Floors.sum = 2774435794 := by decide +kernel

theorem l99PeriodTail096_lower : (2774435794 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk96.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail096_checked
  simpa only [l99PeriodTail096_sum, Nat.cast_ofNat] using h


def l99PeriodTail097Floors : List ℕ := [
  76618706, 46435355, 223979802, 272970026, 65358178, 106508927, 83099772, 130609020, 117408105, 70349277, 93037081, 54670967, 210481099, 227058148, 78087817, 150726335,
  143873524, 64164334, 199465346, 186864786
]

theorem l99PeriodTail097_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk97.filter selectedCellPredicate) l99PeriodTail097Floors = true := by decide +kernel

theorem l99PeriodTail097_sum : l99PeriodTail097Floors.sum = 2601766605 := by decide +kernel

theorem l99PeriodTail097_lower : (2601766605 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk97.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail097_checked
  simpa only [l99PeriodTail097_sum, Nat.cast_ofNat] using h


def l99PeriodTail098Floors : List ℕ := [
  64284077, 115729308, 111099176, 209376662, 178951665, 91643947, 88370343, 167597295, 156422212, 68643696, 71964765, 137181741, 118953591, 56813243, 174090450, 159779615,
  147163715, 125524853, 116338947, 99115303
]

theorem l99PeriodTail098_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk98.filter selectedCellPredicate) l99PeriodTail098Floors = true := by decide +kernel

theorem l99PeriodTail098_sum : l99PeriodTail098Floors.sum = 2459044604 := by decide +kernel

theorem l99PeriodTail098_lower : (2459044604 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk98.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail098_checked
  simpa only [l99PeriodTail098_sum, Nat.cast_ofNat] using h


def l99PeriodTail099Floors : List ℕ := [
  92356646, 78424094, 73417749, 68875960, 64742974, 118490784, 116373585, 104537944, 103004208, 93495369, 92348912, 84544209, 77688793, 66124351, 61164704, 52014309,
  48385185, 41020975, 38345544, 32331229
]

theorem l99PeriodTail099_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk99.filter selectedCellPredicate) l99PeriodTail099Floors = true := by decide +kernel

theorem l99PeriodTail099_sum : l99PeriodTail099Floors.sum = 1507687524 := by decide +kernel

theorem l99PeriodTail099_lower : (1507687524 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk99.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail099_checked
  simpa only [l99PeriodTail099_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
