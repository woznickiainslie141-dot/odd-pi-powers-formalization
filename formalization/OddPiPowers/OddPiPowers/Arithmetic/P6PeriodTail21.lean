module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail21Floors : List ℕ := [
  57755308, 389421161, 383583334, 55937170, 70712408, 397744442, 123273086, 157786491, 105807647, 130088723, 204764096, 153726374, 73591063, 197931328, 112350174, 191652161, 85314576, 329615388, 346359340, 79371684, 222991985, 137222427, 129027673, 215655946, 267564862, 187288921, 42999100, 107917772, 99771248, 223167173, 193893768, 170025651, 150309210, 234476775, 199734489, 172181223, 124967928, 87854817, 304207724, 74983670
]

theorem p6PeriodTail21_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk21.filter selectedCellPredicate) p6PeriodTail21Floors = true := by decide

theorem p6PeriodTail21_sum : p6PeriodTail21Floors.sum = 6993028316 := by decide

theorem p6PeriodTail21_lower : (6993028316 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk21.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail21_checked
  simpa only [p6PeriodTail21_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
