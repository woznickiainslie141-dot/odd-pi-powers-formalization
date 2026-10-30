module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail140Floors : List ℕ := [
  126022820, 143930646, 92711205, 56732193, 279874936, 273717589, 58524351, 80590462, 133148286, 105480071, 156517125, 154508513, 93416393, 115657303, 75063495, 49778693,
  245779303, 200589049, 43584262, 65040812
]

theorem l99PeriodTail140_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk140.filter selectedCellPredicate) l99PeriodTail140Floors = true := by decide +kernel

theorem l99PeriodTail140_sum : l99PeriodTail140Floors.sum = 2550667507 := by decide +kernel

theorem l99PeriodTail140_lower : (2550667507 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk140.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail140_checked
  simpa only [l99PeriodTail140_sum, Nat.cast_ofNat] using h


def l99PeriodTail141Floors : List ℕ := [
  107515611, 92972782, 126545081, 125019026, 82511787, 102215244, 60841961, 239785662, 255495553, 62947353, 104104520, 82565018, 132889238, 121271826, 80084503, 107530509,
  64034604, 272006962, 228020338, 60908828
]

theorem l99PeriodTail141_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk141.filter selectedCellPredicate) l99PeriodTail141Floors = true := by decide +kernel

theorem l99PeriodTail141_sum : l99PeriodTail141Floors.sum = 2509266406 := by decide +kernel

theorem l99PeriodTail141_lower : (2509266406 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk141.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail141_checked
  simpa only [l99PeriodTail141_sum, Nat.cast_ofNat] using h


def l99PeriodTail142Floors : List ℕ := [
  100775804, 79962860, 118862811, 108538761, 71712576, 88923006, 52975097, 191684137, 187687514, 46312016, 76653947, 55316939, 90492222, 81425552, 48440978, 66767757,
  39790676, 157171638, 172885814, 62981286
]

theorem l99PeriodTail142_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk142.filter selectedCellPredicate) l99PeriodTail142Floors = true := by decide +kernel

theorem l99PeriodTail142_sum : l99PeriodTail142Floors.sum = 1899361391 := by decide +kernel

theorem l99PeriodTail142_lower : (1899361391 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk142.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail142_checked
  simpa only [l99PeriodTail142_sum, Nat.cast_ofNat] using h


def l99PeriodTail143Floors : List ℕ := [
  124425290, 122416934, 54423421, 178529748, 174326003, 62920071, 113068942, 111328183, 55023821, 178825494, 158912875, 57397782, 113519185, 122016710, 55309356, 178387314,
  174548487, 62130355, 113481159, 121205275
]

theorem l99PeriodTail143_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk143.filter selectedCellPredicate) l99PeriodTail143Floors = true := by decide +kernel

theorem l99PeriodTail143_sum : l99PeriodTail143Floors.sum = 2332196405 := by decide +kernel

theorem l99PeriodTail143_lower : (2332196405 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk143.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail143_checked
  simpa only [l99PeriodTail143_sum, Nat.cast_ofNat] using h


def l99PeriodTail144Floors : List ℕ := [
  59964301, 191038388, 160368816, 57117158, 113067928, 111539029, 50959233, 150838074, 196483624, 96314339, 95062753, 202006005, 181743635, 96585947, 95377926, 187221322,
  182652376, 89664782, 88583882, 187387109
]

theorem l99PeriodTail144_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk144.filter selectedCellPredicate) l99PeriodTail144Floors = true := by decide +kernel

theorem l99PeriodTail144_sum : l99PeriodTail144Floors.sum = 2593976627 := by decide +kernel

theorem l99PeriodTail144_lower : (2593976627 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk144.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail144_checked
  simpa only [l99PeriodTail144_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
