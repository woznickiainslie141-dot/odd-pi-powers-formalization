module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-! Rational logarithm certificates from a finite atanh series. -/

@[expose] public section

namespace OddPiPowers

open scoped BigOperators

def logSeries (x : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)

def logSeriesError (x : ℚ) (n : ℕ) : ℚ :=
  2 * ((x - 1) / (x + 1)) ^ (2 * n + 1) / (1 - ((x - 1) / (x + 1)) ^ 2)

theorem logSeries_bounds (x : ℚ) (hx : 1 ≤ x) (n : ℕ) :
    (logSeries x n : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ (logSeries x n : ℝ) + (logSeriesError x n : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  let r : ℝ := ((x : ℝ) - 1) / ((x : ℝ) + 1)
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hden.le
  have hr1 : r < 1 := (div_lt_one hden).mpr (by linarith)
  have heq : (1 + r) / (1 - r) = (x : ℝ) := by
    dsimp [r]
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hr0 hr1 n
  have hu := Real.log_div_le_sum_range_add hr0 hr1 n
  rw [heq] at hl hu
  have hs : (logSeries x n : ℝ) =
      2 * ∑ i ∈ Finset.range n, r ^ (2 * i + 1) / (2 * i + 1) := by
    simp only [logSeries, r]
    push_cast
    rfl
  have herr : (logSeriesError x n : ℝ) = 2 * r ^ (2 * n + 1) / (1 - r ^ 2) := by
    simp only [logSeriesError, r]
    push_cast
    rfl
  rw [hs, herr, mul_div_assoc]
  constructor <;> linarith only [hl, hu]

end OddPiPowers
