module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail065Floors : List ℕ := [
  152139097, 165099108, 93451405, 109908628, 54636791, 180537347, 210269782, 78002450, 170003735, 103503617, 73392938, 105264718, 66546225, 295294809, 266448511, 63265465,
  98782310, 73582258, 102296601, 140209369
]

theorem l99PeriodTail065_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk65.filter selectedCellPredicate) l99PeriodTail065Floors = true := by decide +kernel

theorem l99PeriodTail065_sum : l99PeriodTail065Floors.sum = 2602635164 := by decide +kernel

theorem l99PeriodTail065_lower : (2602635164 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk65.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail065_checked
  simpa only [l99PeriodTail065_sum, Nat.cast_ofNat] using h


def l99PeriodTail066Floors : List ℕ := [
  57906497, 166769131, 180663970, 70172407, 69143071, 129981181, 144912501, 114580751, 85130759, 76795742, 119598958, 96247857, 68600754, 54568504, 40738691, 434537456,
  458136755, 49676439, 66906247, 85433636
]

theorem l99PeriodTail066_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk66.filter selectedCellPredicate) l99PeriodTail066Floors = true := by decide +kernel

theorem l99PeriodTail066_sum : l99PeriodTail066Floors.sum = 2570501307 := by decide +kernel

theorem l99PeriodTail066_lower : (2570501307 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk66.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail066_checked
  simpa only [l99PeriodTail066_sum, Nat.cast_ofNat] using h


def l99PeriodTail067Floors : List ℕ := [
  112893595, 144118007, 94947398, 127220070, 161396823, 63885694, 147596796, 181655318, 99239175, 112182437, 66909831, 230836302, 208392971, 63593398, 113469809, 98247457,
  161631315, 181556091, 134004076, 95049807
]

theorem l99PeriodTail067_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk67.filter selectedCellPredicate) l99PeriodTail067Floors = true := by decide +kernel

theorem l99PeriodTail067_sum : l99PeriodTail067Floors.sum = 2598826370 := by decide +kernel

theorem l99PeriodTail067_lower : (2598826370 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk67.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail067_checked
  simpa only [l99PeriodTail067_sum, Nat.cast_ofNat] using h


def l99PeriodTail068Floors : List ℕ := [
  75321959, 121122268, 85592396, 63696304, 45461084, 355417150, 414969793, 57779564, 82355066, 105987551, 156675682, 110252137, 156047663, 124860564, 74069265, 83885169,
  222078156, 185870934, 79222830, 68713292
]

theorem l99PeriodTail068_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk68.filter selectedCellPredicate) l99PeriodTail068Floors = true := by decide +kernel

theorem l99PeriodTail068_sum : l99PeriodTail068Floors.sum = 2669378827 := by decide +kernel

theorem l99PeriodTail068_lower : (2669378827 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk68.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail068_checked
  simpa only [l99PeriodTail068_sum, Nat.cast_ofNat] using h


def l99PeriodTail069Floors : List ℕ := [
  113283292, 117789504, 87163496, 120367608, 79188564, 51383304, 327698123, 313595286, 55205006, 76627460, 113521342, 73903227, 105446543, 145178638, 61363684, 162848460,
  148159861, 58428781, 144868866, 164670493
]

theorem l99PeriodTail069_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk69.filter selectedCellPredicate) l99PeriodTail069Floors = true := by decide +kernel

theorem l99PeriodTail069_sum : l99PeriodTail069Floors.sum = 2520691538 := by decide +kernel

theorem l99PeriodTail069_lower : (2520691538 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk69.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail069_checked
  simpa only [l99PeriodTail069_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
