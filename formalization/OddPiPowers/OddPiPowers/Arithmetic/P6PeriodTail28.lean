module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail28Floors : List ℕ := [
  209841782, 243120113, 195726915, 189197660, 146391808, 141665972, 102874006, 99656872, 64392218, 62439573, 30287210, 29395804, 39573772, 37957501, 72876533, 70016904, 100983527, 97170614, 124759534, 120220284, 144905427, 139818279, 161993280, 130415931, 126066502, 97544870, 94396699, 68548885, 66405702, 42907655, 41606816, 20182125, 19588265, 19774064, 18966706, 36415609
]

theorem p6PeriodTail28_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk28.filter selectedCellPredicate) p6PeriodTail28Floors = true := by decide

theorem p6PeriodTail28_sum : p6PeriodTail28Floors.sum = 3408085417 := by decide

theorem p6PeriodTail28_lower : (3408085417 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk28.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail28_checked
  simpa only [p6PeriodTail28_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
