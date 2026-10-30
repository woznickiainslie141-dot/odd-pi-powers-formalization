module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail15Floors : List ℕ := [
  90563309, 98269544, 1104587650, 121006904, 128567991, 136860611, 145982278, 156047312, 139325368, 119714226, 96690186, 69615324, 37707357, 146808899, 155840039, 165730968, 176594402, 188562154, 201789152, 216458480, 232787755, 251037238, 201584215, 69936070, 144241014, 150375873, 93134560, 291815163, 311929520, 278498154, 93637404, 182068973, 62500234, 259610590, 276083599, 71780013, 222395855, 154437551, 159669262
]

theorem p6PeriodTail15_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk15.filter selectedCellPredicate) p6PeriodTail15Floors = true := by decide

theorem p6PeriodTail15_sum : p6PeriodTail15Floors.sum = 7204245197 := by decide

theorem p6PeriodTail15_lower : (7204245197 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk15.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail15_checked
  simpa only [p6PeriodTail15_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
