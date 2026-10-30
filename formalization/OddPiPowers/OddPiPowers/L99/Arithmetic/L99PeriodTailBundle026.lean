module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail130Floors : List ℕ := [
  107465884, 68148603, 43148868, 257320928, 254689826, 46027710, 66333746, 95223719, 77624348, 117286768, 99515193, 61992658, 79150899, 193771975, 211384077, 90032839,
  81558583, 142068480, 186885278, 137121175
]

theorem l99PeriodTail130_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk130.filter selectedCellPredicate) l99PeriodTail130Floors = true := by decide +kernel

theorem l99PeriodTail130_sum : l99PeriodTail130Floors.sum = 2416751557 := by decide +kernel

theorem l99PeriodTail130_lower : (2416751557 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk130.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail130_checked
  simpa only [l99PeriodTail130_sum, Nat.cast_ofNat] using h


def l99PeriodTail131Floors : List ℕ := [
  102308354, 77175865, 132741188, 108030662, 90658818, 72297090, 59000778, 49063603, 574597534, 401948240, 39742335, 51919075, 68573156, 85452201, 109437972, 145171413,
  91941065, 109879940, 133636527, 153259723
]

theorem l99PeriodTail131_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk131.filter selectedCellPredicate) l99PeriodTail131Floors = true := by decide +kernel

theorem l99PeriodTail131_sum : l99PeriodTail131Floors.sum = 2656835539 := by decide +kernel

theorem l99PeriodTail131_lower : (2656835539 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk131.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail131_checked
  simpa only [l99PeriodTail131_sum, Nat.cast_ofNat] using h


def l99PeriodTail132Floors : List ℕ := [
  124627357, 70908097, 77742135, 180359835, 162713635, 60713483, 132990378, 138436102, 83458278, 48534156, 236698510, 234175893, 51700561, 87746862, 145039972, 126120304,
  57085601, 164119692, 165423522, 70507700
]

theorem l99PeriodTail132_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk132.filter selectedCellPredicate) l99PeriodTail132Floors = true := by decide +kernel

theorem l99PeriodTail132_sum : l99PeriodTail132Floors.sum = 2419102073 := by decide +kernel

theorem l99PeriodTail132_lower : (2419102073 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk132.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail132_checked
  simpa only [l99PeriodTail132_sum, Nat.cast_ofNat] using h


def l99PeriodTail133Floors : List ℕ := [
  69222020, 120643220, 135325779, 107644427, 80362761, 72780887, 123354828, 92081017, 71362344, 52550061, 42897840, 424203803, 456818265, 54315670, 67708260, 93423829,
  115140951, 160194427, 97986330, 131971383
]

theorem l99PeriodTail133_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk133.filter selectedCellPredicate) l99PeriodTail133Floors = true := by decide +kernel

theorem l99PeriodTail133_sum : l99PeriodTail133Floors.sum = 2569988102 := by decide +kernel

theorem l99PeriodTail133_lower : (2569988102 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk133.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail133_checked
  simpa only [l99PeriodTail133_sum, Nat.cast_ofNat] using h


def l99PeriodTail134Floors : List ℕ := [
  168515377, 67043151, 167606456, 192984301, 114968023, 130644259, 72238032, 250929025, 248006535, 70329359, 126005826, 109640449, 181471836, 144053178, 61433963, 152796046,
  108986265, 79514848, 118597360, 91876958
]

theorem l99PeriodTail134_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk134.filter selectedCellPredicate) l99PeriodTail134Floors = true := by decide +kernel

theorem l99PeriodTail134_sum : l99PeriodTail134Floors.sum = 2657641247 := by decide +kernel

theorem l99PeriodTail134_lower : (2657641247 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk134.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail134_checked
  simpa only [l99PeriodTail134_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
