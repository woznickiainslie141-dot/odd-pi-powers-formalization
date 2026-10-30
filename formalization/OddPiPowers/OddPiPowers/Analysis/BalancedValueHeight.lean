module

public import OddPiPowers.Analysis.BalancedLocalHeight
public import Mathlib.Analysis.Complex.Basic

/-! Heights of the actual auxiliary coefficients evaluated at i. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators

theorem auxiliaryScale_abs_le (M n j : ℕ) :
    |auxiliaryScale M n j| ≤ (Nat.factorial (M - 1) : ℚ) * (intervalLcm n : ℚ) ^ (M - 1) := by
  have hs : 0 ≤ auxiliaryScale M n j := by unfold auxiliaryScale; positivity
  rw [abs_of_nonneg hs, auxiliaryScale]
  exact div_le_self (by positivity)
    (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)))

noncomputable def balancedValueMajorant (M n : ℕ) : ℚ :=
  ((n : ℚ) + 1) * ((Nat.factorial (M - 1) : ℚ) * (intervalLcm n : ℚ) ^ (M - 1)) *
    balancedLocalMajorant M (M - 1) n

theorem balancedValueMajorant_pos (M n : ℕ) : 0 < balancedValueMajorant M n := by
  have hd : (0 : ℚ) < intervalLcm n := by exact_mod_cast intervalLcm_pos n
  have hf : (0 : ℚ) < Nat.factorial (M - 1) := by exact_mod_cast Nat.factorial_pos (M - 1)
  unfold balancedValueMajorant balancedLocalMajorant
  positivity

theorem balanced_actualAuxiliary_evalI_bound (M n : ℕ) (h j : Fin M) :
    ‖(actualAuxiliary (balancedActualFamily M n) h j).eval₂ (Rat.castHom ℂ) Complex.I‖ ≤
      ((balancedValueMajorant M n : ℚ) : ℝ) := by
  classical
  have hlocal (ell : ℕ) (hell : ell ≤ n) :
      |auxiliaryScale M n j.val * (balancedActualFamily M n).localCoefficient ell h.val j.val| ≤
        (Nat.factorial (M - 1) : ℚ) * (intervalLcm n : ℚ) ^ (M - 1) *
          balancedLocalMajorant M (M - 1) n := by
    rw [abs_mul]
    exact mul_le_mul (auxiliaryScale_abs_le M n j.val)
      (balanced_localCoefficient_abs_le M n ell h.val j.val hell (by omega))
      (abs_nonneg _) (by positivity)
  simp only [actualAuxiliary, balancedActualFamily, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  calc
    _ ≤ ∑ ell ∈ Finset.range (n + 1),
        ‖((auxiliaryScale M n j.val * (balancedActualFamily M n).localCoefficient ell h.val j.val : ℚ) : ℂ) *
          Complex.I ^ (n - ell)‖ := norm_sum_le _ _
    _ ≤ ∑ ell ∈ Finset.range (n + 1),
        (((Nat.factorial (M - 1) : ℚ) * (intervalLcm n : ℚ) ^ (M - 1) *
          balancedLocalMajorant M (M - 1) n : ℚ) : ℝ) := by
      apply Finset.sum_le_sum
      intro ell hell
      rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_ratCast]
      exact_mod_cast hlocal ell (by have := Finset.mem_range.mp hell; omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, balancedValueMajorant]
      push_cast
      ring

theorem balancedValueMajorant_factorization (M n : ℕ) :
    balancedValueMajorant M n =
      ((Nat.factorial (M - 1) : ℚ) * ((M + 2 * (M - 1) + 1 : ℕ) : ℚ) ^ (M - 1)) *
        (intervalLcm n : ℚ) ^ (M - 1) * ((n : ℚ) + 1) ^ (2 * (M - 1) + 1) *
          (2 : ℚ) ^ (M * n) := by
  unfold balancedValueMajorant balancedLocalMajorant
  rw [pow_succ]
  ring

end OddPiPowers
