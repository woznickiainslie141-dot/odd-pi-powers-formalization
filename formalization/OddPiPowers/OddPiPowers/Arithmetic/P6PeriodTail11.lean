module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail11Floors : List ℕ := [
  57498112, 424034495, 329375921, 64793181, 84352663, 389800927, 142474599, 156719081, 173132814, 196736226, 121510884, 142191000, 80573662, 291297305, 306616094, 257151884, 119650988, 69200087, 188374667, 213911058, 180482545, 123457671, 193654444, 190883307, 159587746, 135405488, 430178404, 89279110, 88662394, 62156915, 53015771, 534372395, 542297749, 54664349, 64254059, 76609864, 74326999, 280064190, 143965999, 144312364
]

theorem p6PeriodTail11_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk11.filter selectedCellPredicate) p6PeriodTail11Floors = true := by decide

theorem p6PeriodTail11_sum : p6PeriodTail11Floors.sum = 7431027411 := by decide

theorem p6PeriodTail11_lower : (7431027411 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk11.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail11_checked
  simpa only [p6PeriodTail11_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
