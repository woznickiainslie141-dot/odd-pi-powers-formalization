module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail18Floors : List ℕ := [
  212437594, 149653404, 68717187, 148515566, 255335438, 304426651, 289193475, 63990117, 141152518, 120619064, 195283753, 257767261, 186654282, 117835077, 257895355, 69756692, 53580771, 408540359, 336569220, 57043750, 74939146, 356554679, 134693869, 205558013, 182562436, 174503912, 67663652, 153368606, 289032012, 55052357, 325300541, 297000786, 67591634, 82691100, 235867791, 177367884, 140875331, 199347205, 63472586, 288340849
]

theorem p6PeriodTail18_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk18.filter selectedCellPredicate) p6PeriodTail18Floors = true := by decide

theorem p6PeriodTail18_sum : p6PeriodTail18Floors.sum = 7266751923 := by decide

theorem p6PeriodTail18_lower : (7266751923 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk18.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail18_checked
  simpa only [p6PeriodTail18_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
