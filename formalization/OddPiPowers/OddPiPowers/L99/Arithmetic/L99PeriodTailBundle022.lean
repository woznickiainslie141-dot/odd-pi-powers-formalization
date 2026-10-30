module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail110Floors : List ℕ := [
  66702534, 291434522, 266625448, 50624422, 74354237, 109886589, 92433912, 144313368, 127086270, 88320201, 114928639, 62154885, 235531632, 216495047, 55372206, 83446913,
  158945035, 149162053, 71190382, 201188125
]

theorem l99PeriodTail110_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk110.filter selectedCellPredicate) l99PeriodTail110Floors = true := by decide +kernel

theorem l99PeriodTail110_sum : l99PeriodTail110Floors.sum = 2660196420 := by decide +kernel

theorem l99PeriodTail110_lower : (2660196420 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk110.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail110_checked
  simpa only [l99PeriodTail110_sum, Nat.cast_ofNat] using h


def l99PeriodTail111Floors : List ℕ := [
  184419741, 58104313, 111559561, 97627739, 195855870, 177419855, 82591183, 78878735, 147578297, 135405432, 68491273, 189816939, 157201608, 130224705, 107725434, 88821418,
  72832951, 59230125, 54394630, 50128061
]

theorem l99PeriodTail111_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk111.filter selectedCellPredicate) l99PeriodTail111Floors = true := by decide +kernel

theorem l99PeriodTail111_sum : l99PeriodTail111Floors.sum = 2248307870 := by decide +kernel

theorem l99PeriodTail111_lower : (2248307870 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk111.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail111_checked
  simpa only [l99PeriodTail111_sum, Nat.cast_ofNat] using h


def l99PeriodTail112Floors : List ℕ := [
  100483110, 96508207, 92677687, 89030242, 85581294, 76452151, 68709781, 62086843, 56377453, 51420983, 47090618, 43285167, 1107056235, 564896396, 27766408, 34044926,
  41387787, 50022801, 60239688, 72411026
]

theorem l99PeriodTail112_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk112.filter selectedCellPredicate) l99PeriodTail112Floors = true := by decide +kernel

theorem l99PeriodTail112_sum : l99PeriodTail112Floors.sum = 2827528803 := by decide +kernel

theorem l99PeriodTail112_lower : (2827528803 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk112.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail112_checked
  simpa only [l99PeriodTail112_sum, Nat.cast_ofNat] using h


def l99PeriodTail113Floors : List ℕ := [
  80806036, 90750802, 102651791, 117058080, 134725933, 156720265, 88362729, 96216518, 113255784, 124304085, 137051956, 151866832, 157133898, 162626027, 129814000, 69094025,
  72130737, 154209213, 169070671, 90796314
]

theorem l99PeriodTail113_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk113.filter selectedCellPredicate) l99PeriodTail113Floors = true := by decide +kernel

theorem l99PeriodTail113_sum : l99PeriodTail113Floors.sum = 2398645696 := by decide +kernel

theorem l99PeriodTail113_lower : (2398645696 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk113.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail113_checked
  simpa only [l99PeriodTail113_sum, Nat.cast_ofNat] using h


def l99PeriodTail114Floors : List ℕ := [
  95392919, 206046342, 169556544, 59702487, 124595621, 121876501, 69016657, 203255609, 223577234, 72945897, 65630404, 110390729, 106280981, 79549114, 110654089, 63496929,
  268924766, 244222823, 51256065, 84522805
]

theorem l99PeriodTail114_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk114.filter selectedCellPredicate) l99PeriodTail114Floors = true := by decide +kernel

theorem l99PeriodTail114_sum : l99PeriodTail114Floors.sum = 2530894516 := by decide +kernel

theorem l99PeriodTail114_lower : (2530894516 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk114.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail114_checked
  simpa only [l99PeriodTail114_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
