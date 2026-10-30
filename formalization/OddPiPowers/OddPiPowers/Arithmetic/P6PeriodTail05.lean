module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.CellWindowAggregate

/-! Candidate finite-tail floors, requiring ordinary kernel checking. -/

@[expose] public section
namespace OddPiPowers.PrimeRates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def p6PeriodTail05Floors : List ℕ := [
  91829089, 456260926, 147886336, 151675417, 152990714, 157843761, 191069427, 236019985, 260375201, 263466173, 97519214, 204785735, 74974751, 340784549, 346447866, 62217387, 215363525, 130278532, 287046128, 242186328, 165664353, 62513687, 267725759, 187686020, 160081294, 57219633, 187060849, 154239524, 129359651, 88040338, 374588063, 80026948, 66907098, 56769174, 554038503, 529900338, 72443743, 72618589, 86065690, 86357489
]

theorem p6PeriodTail05_checked : tailBlockCheck 100000000000000 32 1000000
    (twelveLayerCellChunk5.filter selectedCellPredicate) p6PeriodTail05Floors = true := by decide

theorem p6PeriodTail05_sum : p6PeriodTail05Floors.sum = 7550327787 := by decide

theorem p6PeriodTail05_lower : (7550327787 : ℝ) / 100000000000000 ≤
    ((twelveLayerCellChunk5.filter selectedCellPredicate).map
      (fun c => (periodTailRational 32 1000000 c : ℝ))).sum := by
  have h := tailBlockCheck_sound 100000000000000 32 1000000 _ _ p6PeriodTail05_checked
  simpa only [p6PeriodTail05_sum, Nat.cast_ofNat] using h

end OddPiPowers.PrimeRates
