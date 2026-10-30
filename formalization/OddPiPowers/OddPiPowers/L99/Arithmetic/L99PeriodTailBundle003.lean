module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail015Floors : List ℕ := [
  322787330, 50774632, 63628713, 82071395, 109891461, 154743672, 111158196, 139659142, 168684553, 62976696, 159027411, 200330688, 121031749, 129159559, 77633773, 254203672,
  257189296, 79733671, 133898190, 126893069
]

theorem l99PeriodTail015_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk15.filter selectedCellPredicate) l99PeriodTail015Floors = true := by decide +kernel

theorem l99PeriodTail015_sum : l99PeriodTail015Floors.sum = 2805476868 := by decide +kernel

theorem l99PeriodTail015_lower : (2805476868 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk15.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail015_checked
  simpa only [l99PeriodTail015_sum, Nat.cast_ofNat] using h


def l99PeriodTail016Floors : List ℕ := [
  212996521, 159499834, 68707023, 185978634, 135241052, 108779836, 151529498, 117986545, 88893272, 69379696, 51374746, 468070995, 434621172, 43949588, 58324530, 73110665,
  94335741, 116652215, 74560621, 97295303
]

theorem l99PeriodTail016_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk16.filter selectedCellPredicate) l99PeriodTail016Floors = true := by decide +kernel

theorem l99PeriodTail016_sum : l99PeriodTail016Floors.sum = 2811287487 := by decide +kernel

theorem l99PeriodTail016_lower : (2811287487 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk16.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail016_checked
  simpa only [l99PeriodTail016_sum, Nat.cast_ofNat] using h


def l99PeriodTail017Floors : List ℕ := [
  119462867, 150180349, 114078114, 65454171, 72224882, 183569746, 155177529, 58472177, 139946860, 148557272, 82959762, 52952743, 219855058, 242416005, 58742633, 85471188,
  154660618, 136192045, 62174120, 166625070
]

theorem l99PeriodTail017_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk17.filter selectedCellPredicate) l99PeriodTail017Floors = true := by decide +kernel

theorem l99PeriodTail017_sum : l99PeriodTail017Floors.sum = 2469173209 := by decide +kernel

theorem l99PeriodTail017_lower : (2469173209 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk17.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail017_checked
  simpa only [l99PeriodTail017_sum, Nat.cast_ofNat] using h


def l99PeriodTail018Floors : List ℕ := [
  184690173, 79606965, 72608095, 127613174, 196159841, 147357378, 112505121, 86894951, 137201287, 112046605, 94217610, 75606270, 62013830, 51784536, 576090181, 420138704,
  42495823, 55748026, 74003163, 92797028
]

theorem l99PeriodTail018_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk18.filter selectedCellPredicate) l99PeriodTail018Floors = true := by decide +kernel

theorem l99PeriodTail018_sum : l99PeriodTail018Floors.sum = 2801578761 := by decide +kernel

theorem l99PeriodTail018_lower : (2801578761 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk18.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail018_checked
  simpa only [l99PeriodTail018_sum, Nat.cast_ofNat] using h


def l99PeriodTail019Floors : List ℕ := [
  119791558, 160569949, 102689054, 123752409, 152037077, 176556879, 145397852, 83468349, 92139718, 216325282, 181770219, 68535540, 58151036, 127291472, 129248669, 92668130,
  132868727, 79187058, 54945861, 304029910
]

theorem l99PeriodTail019_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk19.filter selectedCellPredicate) l99PeriodTail019Floors = true := by decide +kernel

theorem l99PeriodTail019_sum : l99PeriodTail019Floors.sum = 2601424749 := by decide +kernel

theorem l99PeriodTail019_lower : (2601424749 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk19.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail019_checked
  simpa only [l99PeriodTail019_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
