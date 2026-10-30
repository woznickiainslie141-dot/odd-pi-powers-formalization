module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail025Floors : List ℕ := [
  767115187, 503499891, 37714233, 47483392, 59872526, 75824072, 89821796, 108089821, 132561774, 166405440, 100220440, 114885906, 133024530, 155827022, 110421720, 70450861,
  74995692, 165506328, 190023396, 105973477
]

theorem l99PeriodTail025_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk25.filter selectedCellPredicate) l99PeriodTail025Floors = true := by decide +kernel

theorem l99PeriodTail025_sum : l99PeriodTail025Floors.sum = 3209717504 := by decide +kernel

theorem l99PeriodTail025_lower : (3209717504 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk25.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail025_checked
  simpa only [l99PeriodTail025_sum, Nat.cast_ofNat] using h


def l99PeriodTail026Floors : List ℕ := [
  114450464, 60728441, 183881021, 209535700, 70611994, 164465595, 98600084, 74958609, 105814054, 61544534, 267896379, 253938398, 54644329, 91118597, 148536459, 135857005,
  218338882, 155790053, 65105743, 170788760
]

theorem l99PeriodTail026_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk26.filter selectedCellPredicate) l99PeriodTail026Floors = true := by decide +kernel

theorem l99PeriodTail026_sum : l99PeriodTail026Floors.sum = 2706605101 := by decide +kernel

theorem l99PeriodTail026_lower : (2706605101 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk26.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail026_checked
  simpa only [l99PeriodTail026_sum, Nat.cast_ofNat] using h


def l99PeriodTail027Floors : List ℕ := [
  119386385, 93120627, 135863337, 101606306, 69340188, 53111385, 369916268, 373882393, 54333584, 71169003, 97263680, 130090901, 97193470, 134967927, 167743980, 69284932,
  166795559, 158195893, 61017906, 137644004
]

theorem l99PeriodTail027_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk27.filter selectedCellPredicate) l99PeriodTail027Floors = true := by decide +kernel

theorem l99PeriodTail027_sum : l99PeriodTail027Floors.sum = 2661927728 := by decide +kernel

theorem l99PeriodTail027_lower : (2661927728 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk27.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail027_checked
  simpa only [l99PeriodTail027_sum, Nat.cast_ofNat] using h


def l99PeriodTail028Floors : List ℕ := [
  150742684, 93627040, 60702889, 284541053, 257754937, 65201898, 104568350, 86849162, 124404556, 108790026, 69400023, 83455198, 230492326, 204590641, 68446848, 119641052,
  120732513, 57317067, 173306379, 191946913
]

theorem l99PeriodTail028_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk28.filter selectedCellPredicate) l99PeriodTail028Floors = true := by decide +kernel

theorem l99PeriodTail028_sum : l99PeriodTail028Floors.sum = 2656511555 := by decide +kernel

theorem l99PeriodTail028_lower : (2656511555 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk28.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail028_checked
  simpa only [l99PeriodTail028_sum, Nat.cast_ofNat] using h


def l99PeriodTail029Floors : List ℕ := [
  94288708, 88930819, 163516499, 146829531, 63082997, 184933973, 149420706, 131197267, 107184026, 95532789, 78543124, 70842341, 133863259, 111917328, 102872625, 88382880,
  76753071, 62101859, 54880448, 44778635
]

theorem l99PeriodTail029_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk29.filter selectedCellPredicate) l99PeriodTail029Floors = true := by decide +kernel

theorem l99PeriodTail029_sum : l99PeriodTail029Floors.sum = 2049852885 := by decide +kernel

theorem l99PeriodTail029_lower : (2049852885 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk29.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail029_checked
  simpa only [l99PeriodTail029_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
