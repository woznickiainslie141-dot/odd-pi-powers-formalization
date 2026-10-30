module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail100Floors : List ℕ := [
  30351661, 961083555, 970888479, 34426772, 36696540, 43118273, 46161730, 54042769, 58147014, 67965359, 73551157, 85997774, 87005724, 95161851, 96481143, 106461060,
  108234408, 120721750, 123184039, 67426417
]

theorem l99PeriodTail100_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk100.filter selectedCellPredicate) l99PeriodTail100Floors = true := by decide +kernel

theorem l99PeriodTail100_sum : l99PeriodTail100Floors.sum = 3267107475 := by decide +kernel

theorem l99PeriodTail100_lower : (3267107475 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk100.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail100_checked
  simpa only [l99PeriodTail100_sum, Nat.cast_ofNat] using h


def l99PeriodTail101Floors : List ℕ := [
  79005627, 76664754, 90214095, 96734782, 113442492, 122280978, 143210454, 155310981, 169012804, 111886028, 68278685, 75441481, 147637030, 157477800, 76831737, 85594529,
  180358205, 179878688, 95029255, 106274537
]

theorem l99PeriodTail101_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk101.filter selectedCellPredicate) l99PeriodTail101Floors = true := by decide +kernel

theorem l99PeriodTail101_sum : l99PeriodTail101Floors.sum = 2330564942 := by decide +kernel

theorem l99PeriodTail101_lower : (2330564942 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk101.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail101_checked
  simpa only [l99PeriodTail101_sum, Nat.cast_ofNat] using h


def l99PeriodTail102Floors : List ℕ := [
  209206566, 168225543, 62904307, 120549835, 125789953, 64967965, 203761079, 201360656, 70315631, 157922928, 153061874, 79436413, 48634282, 202214133, 233348160, 60733772,
  103471706, 78341024, 130940350, 125083073
]

theorem l99PeriodTail102_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk102.filter selectedCellPredicate) l99PeriodTail102Floors = true := by decide +kernel

theorem l99PeriodTail102_sum : l99PeriodTail102Floors.sum = 2600269250 := by decide +kernel

theorem l99PeriodTail102_lower : (2600269250 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk102.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail102_checked
  simpa only [l99PeriodTail102_sum, Nat.cast_ofNat] using h


def l99PeriodTail103Floors : List ℕ := [
  78687196, 110182537, 67702026, 45818328, 277293101, 253008861, 56953657, 86830511, 148575321, 131893986, 190042029, 198069048, 136760218, 92401788, 76440965, 117427713,
  74039003, 53559869, 333714269, 356458148
]

theorem l99PeriodTail103_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk103.filter selectedCellPredicate) l99PeriodTail103Floors = true := by decide +kernel

theorem l99PeriodTail103_sum : l99PeriodTail103Floors.sum = 2885858574 := by decide +kernel

theorem l99PeriodTail103_lower : (2885858574 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk103.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail103_checked
  simpa only [l99PeriodTail103_sum, Nat.cast_ofNat] using h


def l99PeriodTail104Floors : List ℕ := [
  61785095, 87694474, 123900095, 97904504, 143508330, 119229459, 72749646, 90765902, 216200778, 207145080, 92166120, 75516770, 138827643, 175078197, 124763663, 91172670,
  67805627, 112714980, 88652966, 67290406
]

theorem l99PeriodTail104_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk104.filter selectedCellPredicate) l99PeriodTail104Floors = true := by decide +kernel

theorem l99PeriodTail104_sum : l99PeriodTail104Floors.sum = 2254872405 := by decide +kernel

theorem l99PeriodTail104_lower : (2254872405 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk104.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail104_checked
  simpa only [l99PeriodTail104_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
