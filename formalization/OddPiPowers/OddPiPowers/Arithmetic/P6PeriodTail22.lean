module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail22Floors : List ℕ := [
  80095232, 69234149, 60441970, 53224601, 1005883095, 488307874, 50079874, 56647309, 64597268, 74347087, 86484427, 666686780, 131718358, 149883981, 143404858, 133076864, 160879148, 127678096, 181233714, 207589413, 240145040, 206368287, 74642401, 191081464, 267278707, 46482210, 250283498, 283097146, 76670240, 246146344, 179010272, 192515547, 136620834, 295538299, 94773626, 57759501, 372216855, 366724382, 55939376, 76076859
]

theorem p6PeriodTail22_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk22.filter selectedCellPredicate) p6PeriodTail22Floors = true := by decide

theorem p6PeriodTail22_sum : p6PeriodTail22Floors.sum = 7700864986 := by decide

theorem p6PeriodTail22_lower : (7700864986 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk22.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail22_checked
  simpa only [p6PeriodTail22_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
