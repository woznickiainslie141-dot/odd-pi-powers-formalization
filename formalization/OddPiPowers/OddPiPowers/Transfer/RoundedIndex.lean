module

public import OddPiPowers.Transfer.RootDistance

/-! Rounding the analytic scale to positive multiples of `L`. -/

@[expose] public section

namespace OddPiPowers

noncomputable def roundedIndex (L N : ℕ) (x : ℝ) : ℕ :=
  L * max (N + 1) ⌈x⌉₊

theorem roundedIndex_positive (L N : ℕ) (x : ℝ) (hL : 0 < L) :
    0 < roundedIndex L N x := by
  apply Nat.mul_pos hL
  exact lt_of_lt_of_le (Nat.succ_pos N) (le_max_left _ _)

theorem roundedIndex_threshold (L N : ℕ) (x : ℝ) (hL : 0 < L) :
    N ≤ roundedIndex L N x := by
  exact (Nat.le_succ N).trans ((le_max_left _ _).trans
    (Nat.le_mul_of_pos_left _ hL))

theorem roundedIndex_lower (L N : ℕ) (x : ℝ) :
    (L : ℝ) * x ≤ (roundedIndex L N x : ℝ) := by
  have hx : x ≤ (max (N + 1) ⌈x⌉₊ : ℕ) :=
    (Nat.le_ceil x).trans (Nat.cast_le.mpr (le_max_right _ _))
  simpa only [roundedIndex, Nat.cast_mul] using
    mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg L)

theorem roundedIndex_upper (L N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (roundedIndex L N x : ℝ) ≤ (L : ℝ) * (x + N + 2) := by
  have hmax : max (N + 1) ⌈x⌉₊ ≤ (N + 1) + ⌈x⌉₊ :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hmaxR : (max (N + 1) ⌈x⌉₊ : ℝ) ≤ (N : ℝ) + 1 + (⌈x⌉₊ : ℝ) := by
    exact_mod_cast hmax
  have hround : (max (N + 1) ⌈x⌉₊ : ℝ) ≤ x + N + 2 := by
    linarith [Nat.ceil_lt_add_one hx]
  simpa only [roundedIndex, Nat.cast_mul, Nat.cast_max, Nat.cast_add, Nat.cast_one] using
    mul_le_mul_of_nonneg_left hround (Nat.cast_nonneg L)

end OddPiPowers
