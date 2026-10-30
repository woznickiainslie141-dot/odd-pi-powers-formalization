module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail06Floors : List ℕ := [
  411453907, 106669422, 150070443, 148651877, 179616951, 113665518, 164994837, 193936497, 231225195, 106501049, 117828668, 63742380, 267483938, 200811527, 55123516, 223934761, 132410040, 216665802, 181679413, 342585651, 92902257, 68309850, 373163110, 378713064, 70516856, 80350068, 300656868, 138978676, 195829066, 182081929, 250355183, 62382173, 287910457, 254520009, 70900468, 326134712, 161906005, 91070634, 209815462, 244141256
]

theorem p6PeriodTail06_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk6.filter selectedCellPredicate) p6PeriodTail06Floors = true := by decide

theorem p6PeriodTail06_sum : p6PeriodTail06Floors.sum = 7449689495 := by decide

theorem p6PeriodTail06_lower : (7449689495 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk6.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail06_checked
  simpa only [p6PeriodTail06_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
