module

public import OddPiPowers.Transfer.RoundedIndex
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exponential algebra used when choosing the auxiliary index. -/

@[expose] public section

namespace OddPiPowers

theorem exp_neg_log_height (B t : ℝ) (hB : 0 < B) (m j : ℕ) :
    Real.exp (-((m : ℝ) * Real.log B + (j : ℝ) * t)) =
      1 / (B ^ m * (Real.exp t) ^ j) := by
  rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hB]
  simp only [one_div]

theorem exp_small_of_scale (B t s : ℝ) (hB : 0 < B) (m j : ℕ)
    (hscale : (m : ℝ) * Real.log B + (j : ℝ) * t + Real.log 2 ≤ s) :
    Real.exp (-s) ≤ (1 / (B ^ m * (Real.exp t) ^ j)) / 2 := by
  have hle := Real.exp_le_exp.mpr (neg_le_neg hscale)
  have heq : Real.exp (-((m : ℝ) * Real.log B + (j : ℝ) * t + Real.log 2)) =
      (1 / (B ^ m * (Real.exp t) ^ j)) / 2 := by
    rw [show -((m : ℝ) * Real.log B + (j : ℝ) * t + Real.log 2) =
      -((m : ℝ) * Real.log B + (j : ℝ) * t) + (-Real.log 2) by ring]
    rw [Real.exp_add, exp_neg_log_height B t hB, Real.exp_neg, Real.exp_log (by norm_num)]
    ring
  exact hle.trans_eq heq

theorem one_scale_factor_eq (B t : ℝ) (hB : 0 < B) (m k : ℕ) (hk : 0 < k) :
    (1 / (B ^ m * (Real.exp t) ^ (k - 1))) / (2 * Real.exp t) =
      Real.exp (-((m : ℝ) * Real.log B + (k : ℝ) * t)) / 2 := by
  rw [exp_neg_log_height B t hB m k]
  have hpow : (Real.exp t) ^ (k - 1) * Real.exp t = (Real.exp t) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_of_lt hk)]
  rw [← hpow]
  field_simp

/-- The rounded scale satisfies both the required lower inequality and an
upper inequality with a constant depending only on the fixed parameters. -/
theorem rounded_rate_bounds (L N m : ℕ) (β B : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (hB : 1 ≤ B) :
    let s := (m : ℝ) * Real.log B + Real.log 2
    let x := s / ((L : ℝ) * β)
    s ≤ β * (roundedIndex L N x : ℝ) ∧
      (roundedIndex L N x : ℝ) ≤ s / β + (L : ℝ) * (N + 2) := by
  dsimp only
  let s : ℝ := (m : ℝ) * Real.log B + Real.log 2
  let x : ℝ := s / ((L : ℝ) * β)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hs : 0 ≤ s := by
    dsimp [s]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hB))
      (Real.log_nonneg (by norm_num))
  have hx : 0 ≤ x := div_nonneg hs (mul_nonneg hL'.le hβ.le)
  have hidentity : (L : ℝ) * x = s / β := by
    dsimp [x]
    field_simp
  have hlower : s ≤ β * (roundedIndex L N x : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (roundedIndex_lower L N x) hβ.le
    rw [hidentity] at h
    have : β * (s / β) = s := by field_simp
    simpa only [this] using h
  have hupper : (roundedIndex L N x : ℝ) ≤ s / β + (L : ℝ) * (N + 2) := by
    have h := roundedIndex_upper L N x hx
    calc
      _ ≤ (L : ℝ) * (x + N + 2) := h
      _ = _ := by rw [mul_add, mul_add, hidentity]; ring
  exact ⟨hlower, hupper⟩

/-- Substitute the rounded upper bound into an exponential, keeping the
rounding loss in a constant independent of `B`. -/
theorem exp_lower_of_index_upper (B β t n C₀ : ℝ) (m k : ℕ)
    (hB : 0 < B) (hβ : 0 < β) (ht : 0 ≤ t)
    (hn : n ≤ ((m : ℝ) * Real.log B + Real.log 2) / β + C₀) :
    (Real.exp (-((k : ℝ) * t) * (Real.log 2 / β + C₀)) / 2) *
        B ^ (-((m : ℝ) + (k : ℝ) * t * m / β)) ≤
      Real.exp (-((m : ℝ) * Real.log B + (k : ℝ) * t * n)) / 2 := by
  let A : ℝ := (k : ℝ) * t
  let E : ℝ := (m : ℝ) + A * m / β
  let C : ℝ := A * (Real.log 2 / β + C₀)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) ht
  have halgebra : (m : ℝ) * Real.log B +
      A * (((m : ℝ) * Real.log B + Real.log 2) / β + C₀) =
        E * Real.log B + C := by
    dsimp [E, C]
    field_simp; ring
  have hupper : (m : ℝ) * Real.log B + A * n ≤ E * Real.log B + C := by
    have h := add_le_add_left (mul_le_mul_of_nonneg_left hn hA) ((m : ℝ) * Real.log B)
    rw [← halgebra]
    linarith
  have hexp : Real.exp (-(E * Real.log B + C)) ≤
      Real.exp (-((m : ℝ) * Real.log B + A * n)) :=
    Real.exp_le_exp.mpr (neg_le_neg hupper)
  have heq : (Real.exp (-C) / 2) * B ^ (-E) =
      Real.exp (-(E * Real.log B + C)) / 2 := by
    rw [Real.rpow_def_of_pos hB, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  have hfinal : (Real.exp (-C) / 2) * B ^ (-E) ≤
      Real.exp (-((m : ℝ) * Real.log B + A * n)) / 2 := by
    rw [heq]
    exact div_le_div_of_nonneg_right hexp (by norm_num)
  simpa only [A, E, C, neg_mul, mul_assoc] using hfinal

end OddPiPowers
