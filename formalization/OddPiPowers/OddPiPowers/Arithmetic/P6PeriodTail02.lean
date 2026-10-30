module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail02Floors : List ℕ := [
  287549832, 190026049, 72553908, 257668727, 149962728, 152198334, 232599856, 91824394, 320873478, 330888376, 70285068, 257037492, 174781156, 177596609, 226520434, 92091626, 376030689, 323966999, 82712658, 302892455, 171926674, 174938745, 142006226, 240897449, 61121959, 311158349, 320718471, 65329800, 265396259, 108158505, 206011351, 209967082, 142232309, 232026965, 73695240, 375834069, 265794299, 67573010, 95152941, 247672627
]

theorem p6PeriodTail02_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk2.filter selectedCellPredicate) p6PeriodTail02Floors = true := by decide

theorem p6PeriodTail02_sum : p6PeriodTail02Floors.sum = 7947673198 := by decide

theorem p6PeriodTail02_lower : (7947673198 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk2.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail02_checked
  simpa only [p6PeriodTail02_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
