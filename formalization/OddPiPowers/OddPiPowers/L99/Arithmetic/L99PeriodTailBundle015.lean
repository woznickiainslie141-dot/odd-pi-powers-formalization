module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail075Floors : List ℕ := [
  42727134, 2231491432, 42713516, 44511832, 46426159, 48466694, 50644782, 52973068, 55465690, 58138484, 61009243, 64098013, 67427443, 71023199, 74914465, 79134534,
  83721524, 88719241, 94178231
]

theorem l99PeriodTail075_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk75.filter selectedCellPredicate) l99PeriodTail075Floors = true := by decide +kernel

theorem l99PeriodTail075_sum : l99PeriodTail075Floors.sum = 3357784684 := by decide +kernel

theorem l99PeriodTail075_lower : (3357784684 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk75.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail075_checked
  simpa only [l99PeriodTail075_sum, Nat.cast_ofNat] using h


def l99PeriodTail076Floors : List ℕ := [
  100157061, 106723896, 113958457, 121954447, 130822602, 140694552, 151727729, 164111693, 87183503, 90892823, 94844014, 99058572, 111526623, 116712966, 122269694, 128232933,
  134643329, 141546733, 148995031, 157047117
]

theorem l99PeriodTail076_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk76.filter selectedCellPredicate) l99PeriodTail076Floors = true := by decide +kernel

theorem l99PeriodTail076_sum : l99PeriodTail076Floors.sum = 2463103775 := by decide +kernel

theorem l99PeriodTail076_lower : (2463103775 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk76.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail076_checked
  simpa only [l99PeriodTail076_sum, Nat.cast_ofNat] using h


def l99PeriodTail077Floors : List ℕ := [
  165770065, 162723347, 159039795, 154619933, 128099722, 66050931, 67441134, 139232214, 145350736, 75097250, 76784384, 158862819, 166336657, 86137798, 88212822, 182958039,
  192218991, 99804905, 102396452, 212982063
]

theorem l99PeriodTail077_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk77.filter selectedCellPredicate) l99PeriodTail077Floors = true := by decide +kernel

theorem l99PeriodTail077_sum : l99PeriodTail077Floors.sum = 2630120057 := by decide +kernel

theorem l99PeriodTail077_lower : (2630120057 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk77.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail077_checked
  simpa only [l99PeriodTail077_sum, Nat.cast_ofNat] using h


def l99PeriodTail078Floors : List ℕ := [
  167340627, 57307943, 117002942, 120297712, 61428194, 175037864, 167580074, 57526905, 117667742, 110260895, 62053294, 174606840, 183121005, 56736800, 129232593, 71664606,
  70179565, 95925332, 54178445, 222414434
]

theorem l99PeriodTail078_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk78.filter selectedCellPredicate) l99PeriodTail078Floors = true := by decide +kernel

theorem l99PeriodTail078_sum : l99PeriodTail078Floors.sum = 2271563812 := by decide +kernel

theorem l99PeriodTail078_lower : (2271563812 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk78.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail078_checked
  simpa only [l99PeriodTail078_sum, Nat.cast_ofNat] using h


def l99PeriodTail079Floors : List ℕ := [
  231976633, 64142515, 100711464, 81896665, 134743451, 127929348, 86894695, 118977997, 67303189, 277127147, 290476395, 80573916, 126732637, 103262726, 170282512, 162120524,
  110378786, 151461254, 85846037, 57852447
]

theorem l99PeriodTail079_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk79.filter selectedCellPredicate) l99PeriodTail079Floors = true := by decide +kernel

theorem l99PeriodTail079_sum : l99PeriodTail079Floors.sum = 2630690338 := by decide +kernel

theorem l99PeriodTail079_lower : (2630690338 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk79.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail079_checked
  simpa only [l99PeriodTail079_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
