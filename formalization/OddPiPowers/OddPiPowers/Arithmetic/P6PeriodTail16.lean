module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail16Floors : List ℕ := [
  336134317, 58327603, 302235515, 321111426, 53315187, 275168674, 114380541, 221606725, 131033536, 66852781, 190873242, 116326009, 215321942, 103044788, 62090456, 386328667, 411639032, 71242843, 255630322, 112647788, 153198182, 136947149, 180189674, 247753488, 205403015, 159016692, 95061984, 185336579, 170505802, 112396130, 330566750, 91644209, 59920650, 496466330, 474531615, 54452460, 82283019, 88993078, 291242435, 116000084
]

theorem p6PeriodTail16_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk16.filter selectedCellPredicate) p6PeriodTail16Floors = true := by decide

theorem p6PeriodTail16_sum : p6PeriodTail16Floors.sum = 7537220719 := by decide

theorem p6PeriodTail16_lower : (7537220719 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk16.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail16_checked
  simpa only [p6PeriodTail16_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
