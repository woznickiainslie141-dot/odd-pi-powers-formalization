module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail01Floors : List ℕ := [
  100015646, 69290261, 72060114, 37499720, 39061177, 176210577, 181466862, 218122215, 224828760, 264970790, 273376215, 282188043, 255003789, 263497183, 233504654, 241549942, 208348594, 215783301, 178898550, 185518592, 144384763, 149932949, 25591865, 313118393, 322456374, 109633124, 222585276, 198733000, 115307115, 353120909, 318779848, 108518514, 252038914, 339829972, 351145681, 311173841, 321892258, 277645146
]

theorem p6PeriodTail01_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk1.filter selectedCellPredicate) p6PeriodTail01Floors = true := by decide

theorem p6PeriodTail01_sum : p6PeriodTail01Floors.sum = 7957082927 := by decide

theorem p6PeriodTail01_lower : (7957082927 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk1.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail01_checked
  simpa only [p6PeriodTail01_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
