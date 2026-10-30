module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail08Floors : List ℕ := [
  80515329, 351329152, 334313541, 57683856, 194365943, 136723479, 167264841, 74624607, 233819422, 207620771, 164871081, 134092380, 159966612, 124971459, 322556088, 71676782, 45359233, 388778877, 493303504, 58525306, 74281439, 254057184, 127844391, 133653285, 172631845, 146069888, 217588850, 231092693, 219720645, 276675782, 105479669, 181779607, 85041259, 59655213, 340025339, 289277397, 68223778, 260484882, 123261904, 141480300
]

theorem p6PeriodTail08_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk8.filter selectedCellPredicate) p6PeriodTail08Floors = true := by decide

theorem p6PeriodTail08_sum : p6PeriodTail08Floors.sum = 7310687613 := by decide

theorem p6PeriodTail08_lower : (7310687613 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk8.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail08_checked
  simpa only [p6PeriodTail08_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
