module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace OddPiPowers.PrimeRates

/-- A fixed reciprocal window; the prime interval is `N/upper < p ≤ N/lower`.
The lower endpoint for `N/p` is closed, the upper one is open. -/
structure PrimeWindow where
  lower : ℝ
  upper : ℝ
  weight : ℕ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper

theorem PrimeWindow.upper_pos (W : PrimeWindow) : 0 < W.upper :=
  W.lower_pos.trans W.lower_lt_upper

theorem PrimeWindow.reciprocal_mem_iff (W : PrimeWindow) {N p : ℝ}
    (hp : 0 < p) :
    N / W.upper < p ∧ p ≤ N / W.lower ↔
      W.lower ≤ N / p ∧ N / p < W.upper := by
  rw [div_lt_iff₀ W.upper_pos, le_div_iff₀ W.lower_pos,
    le_div_iff₀ hp, div_lt_iff₀ hp]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

/-- Fixed windows eventually contain only the large primes retained by P3.
The explicit sufficient threshold is `N > L * upper²`. -/
theorem PrimeWindow.admissible_of_large (W : PrimeWindow) (L N p : ℕ)
    (hcap : 1 ≤ (L : ℝ) * W.lower)
    (hN : (L : ℝ) * W.upper ^ 2 < (N : ℝ))
    (hp : 0 < p)
    (hmem : (N : ℝ) / W.upper < (p : ℝ) ∧
      (p : ℝ) ≤ (N : ℝ) / W.lower) :
    p ≤ L * N ∧ L * N < p * p := by
  have hNR : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg L) (sq_nonneg W.upper)) hN
  have hLR : (0 : ℝ) < (L : ℝ) := by
    by_contra h
    have hnonpos : (L : ℝ) ≤ 0 := le_of_not_gt h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hnonpos W.lower_pos.le]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlu : W.lower ≤ (N : ℝ) / (p : ℝ) ∧
      (N : ℝ) / (p : ℝ) < W.upper :=
    (W.reciprocal_mem_iff hpR).mp hmem
  have hpl : (p : ℝ) * W.lower ≤ N :=
    by simpa only [mul_comm] using (le_div_iff₀ hpR).mp hlu.1
  have hpu : (N : ℝ) < (p : ℝ) * W.upper :=
    (div_lt_iff₀ W.upper_pos).mp hmem.1
  have hsmall : (p : ℝ) ≤ (L : ℝ) * (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hpl (Nat.cast_nonneg L),
      mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg p)]
  have hupper : (L : ℝ) * W.upper < (p : ℝ) := by
    by_contra h
    have hle : (p : ℝ) ≤ (L : ℝ) * W.upper := le_of_not_gt h
    nlinarith [mul_le_mul_of_nonneg_right hle W.upper_pos.le]
  have hlarge : (L : ℝ) * (N : ℝ) < (p : ℝ) * (p : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_left hpu hLR,
      mul_pos hpR (sub_pos.mpr hupper)]
  exact ⟨by exact_mod_cast hsmall, by exact_mod_cast hlarge⟩

end OddPiPowers.PrimeRates

end
