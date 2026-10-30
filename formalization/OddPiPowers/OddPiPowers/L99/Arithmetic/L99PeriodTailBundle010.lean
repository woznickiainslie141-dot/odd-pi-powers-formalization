module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail050Floors : List ℕ := [
  31315224, 981155729, 971039687, 30662722, 36291501, 38737975, 45584506, 48879564, 57322136, 61788493, 72364518, 78479378, 85403497, 86110395, 94442956, 95375934,
  105593829, 106860606, 119682537, 58853657
]

theorem l99PeriodTail050_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk50.filter selectedCellPredicate) l99PeriodTail050Floors = true := by decide +kernel

theorem l99PeriodTail050_sum : l99PeriodTail050Floors.sum = 3205944844 := by decide +kernel

theorem l99PeriodTail050_lower : (3205944844 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk50.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail050_checked
  simpa only [l99PeriodTail050_sum, Nat.cast_ofNat] using h


def l99PeriodTail051Floors : List ℕ := [
  69566506, 74152781, 87128856, 93278371, 109202997, 117495797, 137334712, 148620879, 161357907, 162282104, 57371941, 150152028, 149181780, 78258665, 86643034, 170097690,
  182245255, 89228292, 99650281, 210796358
]

theorem l99PeriodTail051_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk51.filter selectedCellPredicate) l99PeriodTail051Floors = true := by decide +kernel

theorem l99PeriodTail051_sum : l99PeriodTail051Floors.sum = 2434046234 := by decide +kernel

theorem l99PeriodTail051_lower : (2434046234 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk51.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail051_checked
  simpa only [l99PeriodTail051_sum, Nat.cast_ofNat] using h


def l99PeriodTail052Floors : List ℕ := [
  211395356, 112167583, 125827922, 60264546, 188652443, 185877780, 70172830, 134067922, 128746308, 72762881, 229200223, 179773310, 50938789, 86684816, 76924589, 118504567,
  112994020, 83872989, 107498400, 65964491
]

theorem l99PeriodTail052_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk52.filter selectedCellPredicate) l99PeriodTail052Floors = true := by decide +kernel

theorem l99PeriodTail052_sum : l99PeriodTail052Floors.sum = 2402291765 := by decide +kernel

theorem l99PeriodTail052_lower : (2402291765 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk52.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail052_checked
  simpa only [l99PeriodTail052_sum, Nat.cast_ofNat] using h


def l99PeriodTail053Floors : List ℕ := [
  254303241, 226042847, 58577517, 83269788, 142251420, 117041235, 181223227, 188374315, 120498405, 155216655, 103040630, 69877701, 364356709, 285999261, 53550561, 75929526,
  116042389, 91009139, 123678148, 165086482
]

theorem l99PeriodTail053_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk53.filter selectedCellPredicate) l99PeriodTail053Floors = true := by decide +kernel

theorem l99PeriodTail053_sum : l99PeriodTail053Floors.sum = 2975369196 := by decide +kernel

theorem l99PeriodTail053_lower : (2975369196 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk53.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail053_checked
  simpa only [l99PeriodTail053_sum, Nat.cast_ofNat] using h


def l99PeriodTail054Floors : List ℕ := [
  66775951, 185190155, 191647528, 72501471, 69635900, 127069731, 137894466, 105620314, 151144834, 102952731, 74640225, 52241587, 379932047, 390144005, 50488377, 70536465,
  88369996, 125756278, 78636048, 108043857
]

theorem l99PeriodTail054_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk54.filter selectedCellPredicate) l99PeriodTail054Floors = true := by decide +kernel

theorem l99PeriodTail054_sum : l99PeriodTail054Floors.sum = 2629221966 := by decide +kernel

theorem l99PeriodTail054_lower : (2629221966 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk54.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail054_checked
  simpa only [l99PeriodTail054_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
