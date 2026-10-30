module
public import OddPiPowers.L99.Arithmetic.PeriodTailFloor
public import OddPiPowers.L99.Arithmetic.CellWindowAggregate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open OddPiPowers.PrimeRates
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def l99PeriodTail040Floors : List ℕ := [
  55651142, 293092124, 320349026, 67678372, 103933963, 70222942, 103906406, 138858651, 61216749, 170895216, 164837099, 68027356, 177267790, 121278619, 93484774, 134680187,
  100047202, 67267761, 51181742, 345470663
]

theorem l99PeriodTail040_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk40.filter selectedCellPredicate) l99PeriodTail040Floors = true := by decide +kernel

theorem l99PeriodTail040_sum : l99PeriodTail040Floors.sum = 2709347784 := by decide +kernel

theorem l99PeriodTail040_lower : (2709347784 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk40.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail040_checked
  simpa only [l99PeriodTail040_sum, Nat.cast_ofNat] using h


def l99PeriodTail041Floors : List ℕ := [
  395378250, 55757522, 72560829, 98307627, 130662674, 89022176, 122233354, 161204692, 65797305, 156550979, 201865810, 115657344, 135228833, 82465111, 297786676, 218401867,
  53908725, 85723255, 157490103, 141276280
]

theorem l99PeriodTail041_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk41.filter selectedCellPredicate) l99PeriodTail041Floors = true := by decide +kernel

theorem l99PeriodTail041_sum : l99PeriodTail041Floors.sum = 2837279412 := by decide +kernel

theorem l99PeriodTail041_lower : (2837279412 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk41.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail041_checked
  simpa only [l99PeriodTail041_sum, Nat.cast_ofNat] using h


def l99PeriodTail042Floors : List ℕ := [
  60296102, 177670870, 201501858, 81578799, 81425503, 145037928, 181805845, 149172147, 115016601, 97513220, 76745942, 72664643, 129887018, 102745537, 89714802, 68907531,
  57944689, 45604864, 573303665, 579375096
]

theorem l99PeriodTail042_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk42.filter selectedCellPredicate) l99PeriodTail042Floors = true := by decide +kernel

theorem l99PeriodTail042_sum : l99PeriodTail042Floors.sum = 3087912660 := by decide +kernel

theorem l99PeriodTail042_lower : (3087912660 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk42.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail042_checked
  simpa only [l99PeriodTail042_sum, Nat.cast_ofNat] using h


def l99PeriodTail043Floors : List ℕ := [
  46615183, 59336995, 70716343, 85716269, 97896876, 124252589, 69277719, 87331326, 110566207, 141004190, 157496740, 193057944, 154893275, 87302677, 95037698, 234545371,
  178447457, 71378263, 154941725, 93903158
]

theorem l99PeriodTail043_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk43.filter selectedCellPredicate) l99PeriodTail043Floors = true := by decide +kernel

theorem l99PeriodTail043_sum : l99PeriodTail043Floors.sum = 2313718005 := by decide +kernel

theorem l99PeriodTail043_lower : (2313718005 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk43.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail043_checked
  simpa only [l99PeriodTail043_sum, Nat.cast_ofNat] using h


def l99PeriodTail044Floors : List ℕ := [
  71910995, 94921910, 59841721, 243696313, 235995971, 55720610, 86777529, 153831483, 132163638, 59338343, 156036587, 168037329, 70890103, 174349707, 122618140, 88484276,
  130396597, 99786902, 80023338, 61626836
]

theorem l99PeriodTail044_checked :
    tailBlockCheck 100000000000000 32 1000000 (twentyEightLayerCellChunk44.filter selectedCellPredicate) l99PeriodTail044Floors = true := by decide +kernel

theorem l99PeriodTail044_sum : l99PeriodTail044Floors.sum = 2346448328 := by decide +kernel

theorem l99PeriodTail044_lower : (2346448328 : ℝ) / 100000000000000 ≤
    ((twentyEightLayerCellChunk44.filter selectedCellPredicate).map (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ l99PeriodTail044_checked
  simpa only [l99PeriodTail044_sum, Nat.cast_ofNat] using h


end OddPiPowers.L99.PrimeRates
