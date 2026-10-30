module

public import OddPiPowers.Arithmetic.FinitePeriodKernel
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Draft natural-number floor certificates for finite period-gap sums.
No certificate data or native evaluation is introduced here. -/

@[expose] public section

namespace OddPiPowers.L99.PrimeRates

open OddPiPowers.PrimeRates

structure PeriodFloorRow where
  cell : TwentyEightCellCertificate
  period : ℕ
  floor : ℕ
  deriving DecidableEq, Repr

def periodFloorNumerator (row : PeriodFloorRow) : ℕ :=
  row.cell.value * (row.cell.rightNumerator * row.cell.leftDenominator -
    row.cell.leftNumerator * row.cell.rightDenominator)

def periodFloorDenominator (row : PeriodFloorRow) : ℕ :=
  99 * (row.period * row.cell.leftDenominator + row.cell.leftNumerator) *
    (row.period * row.cell.rightDenominator + row.cell.rightNumerator)

/-- Entirely natural-number conditions; `scale` can be `10^14`. -/
def periodFloorCheck (scale : ℕ) (row : PeriodFloorRow) : Bool :=
  decide (0 < scale ∧ 0 < row.cell.leftNumerator ∧
    0 < row.cell.leftDenominator ∧ 0 < row.cell.rightDenominator ∧
    row.cell.leftNumerator * row.cell.rightDenominator <
      row.cell.rightNumerator * row.cell.leftDenominator ∧
    row.floor * periodFloorDenominator row ≤ scale * periodFloorNumerator row)

noncomputable def periodFloorActual (row : PeriodFloorRow) : ℝ :=
  (row.cell.value : ℝ) / 99 * periodGap row.period
    (row.cell.left : ℝ) (row.cell.right : ℝ)

theorem periodFloorActual_eq_fraction (row : PeriodFloorRow)
    (hA : 0 < row.cell.leftNumerator) (hC : 0 < row.cell.leftDenominator)
    (hD : 0 < row.cell.rightDenominator)
    (horder : row.cell.leftNumerator * row.cell.rightDenominator <
      row.cell.rightNumerator * row.cell.leftDenominator) :
    periodFloorActual row = (periodFloorNumerator row : ℝ) /
      (periodFloorDenominator row : ℝ) := by
  have hC' : (0 : ℝ) < row.cell.leftDenominator := by exact_mod_cast hC
  have hD' : (0 : ℝ) < row.cell.rightDenominator := by exact_mod_cast hD
  have hA' : (0 : ℝ) < row.cell.leftNumerator := by exact_mod_cast hA
  have hB : 0 < row.cell.rightNumerator := by
    by_contra h
    have hz : row.cell.rightNumerator = 0 := by omega
    simp [hz] at horder
  have hB' : (0 : ℝ) < row.cell.rightNumerator := by exact_mod_cast hB
  have hleft : 0 < (row.cell.left : ℝ) := by
    simp only [TwentyEightCellCertificate.left, Rat.cast_div, Rat.cast_natCast]
    exact div_pos hA' hC'
  have hright : (row.cell.left : ℝ) ≤ (row.cell.right : ℝ) := by
    simp only [TwentyEightCellCertificate.left, TwentyEightCellCertificate.right,
      Rat.cast_div, Rat.cast_natCast]
    apply (div_le_div_iff₀ hC' hD').2
    exact_mod_cast horder.le
  rw [periodFloorActual, periodGap_eq_fraction row.period hleft hright]
  simp only [TwentyEightCellCertificate.left, TwentyEightCellCertificate.right,
    Rat.cast_div, Rat.cast_natCast, periodFloorNumerator, periodFloorDenominator,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  rw [Nat.cast_sub (Nat.le_of_lt horder)]
  push_cast
  have hrC : (0 : ℝ) < (row.period : ℝ) * row.cell.leftDenominator + row.cell.leftNumerator := by positivity
  have hrD : (0 : ℝ) < (row.period : ℝ) * row.cell.rightDenominator + row.cell.rightNumerator := by positivity
  field_simp [ne_of_gt hC', ne_of_gt hD', ne_of_gt hrC, ne_of_gt hrD]

theorem periodFloorDenominator_pos (row : PeriodFloorRow)
    (hA : 0 < row.cell.leftNumerator) (hC : 0 < row.cell.leftDenominator)
    (hD : 0 < row.cell.rightDenominator)
    (horder : row.cell.leftNumerator * row.cell.rightDenominator <
      row.cell.rightNumerator * row.cell.leftDenominator) :
    0 < periodFloorDenominator row := by
  have hB : 0 < row.cell.rightNumerator := by
    by_contra h
    have hz : row.cell.rightNumerator = 0 := by omega
    simp [hz] at horder
  unfold periodFloorDenominator
  positivity

/-- Exact equivalence of the integer comparison and the real lower bound. -/
theorem periodFloor_cross_iff (scale : ℕ) (row : PeriodFloorRow)
    (hs : 0 < scale) (hA : 0 < row.cell.leftNumerator)
    (hC : 0 < row.cell.leftDenominator) (hD : 0 < row.cell.rightDenominator)
    (horder : row.cell.leftNumerator * row.cell.rightDenominator <
      row.cell.rightNumerator * row.cell.leftDenominator) :
    row.floor * periodFloorDenominator row ≤ scale * periodFloorNumerator row ↔
      (row.floor : ℝ) / scale ≤ periodFloorActual row := by
  rw [periodFloorActual_eq_fraction row hA hC hD horder]
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have hdR : (0 : ℝ) < periodFloorDenominator row := by
    exact_mod_cast periodFloorDenominator_pos row hA hC hD horder
  rw [div_le_div_iff₀ hsR hdR]
  constructor
  · intro h
    have h' : row.floor * periodFloorDenominator row ≤
        periodFloorNumerator row * scale := by simpa [Nat.mul_comm] using h
    exact_mod_cast h'
  · intro h
    have h' : row.floor * periodFloorDenominator row ≤
        periodFloorNumerator row * scale := by exact_mod_cast h
    simpa [Nat.mul_comm] using h'

theorem periodFloorCheck_sound (scale : ℕ) (row : PeriodFloorRow)
    (h : periodFloorCheck scale row = true) :
    (row.floor : ℝ) / scale ≤ periodFloorActual row := by
  have h' := of_decide_eq_true h
  exact (periodFloor_cross_iff scale row h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1
    h'.2.2.2.2.1).1 h'.2.2.2.2.2

def periodFloorListCheck (scale : ℕ) (rows : List PeriodFloorRow) : Bool :=
  rows.all (periodFloorCheck scale)

def periodFloorListNumerator (rows : List PeriodFloorRow) : ℕ :=
  (rows.map PeriodFloorRow.floor).sum

/-- A checked block may be combined with other blocks without a common
rational denominator for the individual period-gap terms. -/
theorem periodFloorListCheck_sound (scale : ℕ) (rows : List PeriodFloorRow)
    (h : periodFloorListCheck scale rows = true) :
    (periodFloorListNumerator rows : ℝ) / scale ≤
      (rows.map periodFloorActual).sum := by
  induction rows with
  | nil => simp [periodFloorListNumerator]
  | cons row rows ih =>
    have hall : (row :: rows).all (periodFloorCheck scale) = true := h
    have hrow : periodFloorCheck scale row = true := by
      exact List.all_eq_true.mp hall row (by simp)
    have htail : periodFloorListCheck scale rows = true := by
      have ht : (rows.all (periodFloorCheck scale)) = true := by
        have hpair : periodFloorCheck scale row = true ∧ rows.all (periodFloorCheck scale) = true := by
          simpa only [List.all_cons, Bool.and_eq_true] using hall
        exact hpair.2
      exact ht
    have hterm := periodFloorCheck_sound scale row hrow
    have hrest := ih htail
    simp only [periodFloorListNumerator, List.map_cons, List.sum_cons, Nat.cast_add,
      add_div]
    exact add_le_add hterm hrest

theorem periodFloorListCheck_append (scale : ℕ) (xs ys : List PeriodFloorRow)
    (hx : periodFloorListCheck scale xs = true)
    (hy : periodFloorListCheck scale ys = true) :
    periodFloorListCheck scale (xs ++ ys) = true := by
  change (xs ++ ys).all (periodFloorCheck scale) = true
  rw [List.all_append]
  simpa only [Bool.and_eq_true, periodFloorListCheck] using And.intro hx hy

end OddPiPowers.L99.PrimeRates
