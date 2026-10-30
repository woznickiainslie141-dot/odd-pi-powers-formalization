module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail24Floors : List ℕ := [
  237496028, 281466697, 102191177, 211155404, 76249050, 339645117, 334061637, 73491493, 200726700, 143373047, 258218921, 170115175, 231289865, 187229246, 154663990, 224852341, 178327034, 120740019, 297986503, 89955319, 71658523, 58428733, 689428945, 445864501, 54817090, 66776623, 83129222, 403409556, 127525580, 129041646, 128006761, 103887467, 154591412, 187132561, 231157081, 164695234, 289628881, 297044229, 291997715, 230050520
]

theorem p6PeriodTail24_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk24.filter selectedCellPredicate) p6PeriodTail24Floors = true := by decide

theorem p6PeriodTail24_sum : p6PeriodTail24Floors.sum = 8121507043 := by decide

theorem p6PeriodTail24_lower : (8121507043 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk24.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail24_checked
  simpa only [p6PeriodTail24_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
