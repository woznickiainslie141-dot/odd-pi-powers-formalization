module

public import OddPiPowers.Analysis.ActualLocalHeight
public import OddPiPowers.Analysis.BalancedValueHeight

/-! The actual general auxiliary coefficients retain the prescribed exponential height. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def actualValueMajorant : ℚ :=
  ((P.n : ℚ) + 1) * ((Nat.factorial (M - 1) : ℚ) * (intervalLcm P.n : ℚ) ^ (M - 1)) *
    actualLocalMajorant P (M - 1)

theorem actualValueMajorant_pos : 0 < actualValueMajorant P := by
  have hd : (0 : ℚ) < intervalLcm P.n := by exact_mod_cast intervalLcm_pos P.n
  have hf : (0 : ℚ) < Nat.factorial (M - 1) := by exact_mod_cast Nat.factorial_pos (M - 1)
  unfold actualValueMajorant
  exact mul_pos (by positivity) (actualLocalMajorant_pos P _)

theorem actualAuxiliary_evalI_height (h j : Fin M) :
    ‖(actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I‖ ≤
      ((actualValueMajorant P : ℚ) : ℝ) := by
  classical
  have hlocal (ell : ℕ) (hell : ell ≤ P.n) :
      |auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val| ≤
        (Nat.factorial (M - 1) : ℚ) * (intervalLcm P.n : ℚ) ^ (M - 1) *
          actualLocalMajorant P (M - 1) := by
    rw [abs_mul]
    exact mul_le_mul (auxiliaryScale_abs_le M P.n j.val)
      (actual_localCoefficient_abs_le P ell h.val j.val hell (by omega))
      (abs_nonneg _) (by positivity)
  simp only [actualAuxiliary, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  calc
    _ ≤ ∑ ell ∈ Finset.range (P.n + 1),
        ‖((auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val : ℚ) : ℂ) *
          Complex.I ^ (P.n - ell)‖ := norm_sum_le _ _
    _ ≤ ∑ ell ∈ Finset.range (P.n + 1),
        (((Nat.factorial (M - 1) : ℚ) * (intervalLcm P.n : ℚ) ^ (M - 1) *
          actualLocalMajorant P (M - 1) : ℚ) : ℝ) := by
      apply Finset.sum_le_sum
      intro ell hell
      rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_ratCast]
      exact_mod_cast hlocal ell (by have := Finset.mem_range.mp hell; omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, actualValueMajorant]
      push_cast
      ring

theorem actualValueMajorant_factorization :
    actualValueMajorant P =
      ((Nat.factorial (M - 1) : ℚ) * ((2 * M + 2 * (M - 1) + 1 : ℕ) : ℚ) ^ (M - 1)) *
        (intervalLcm P.n : ℚ) ^ (M - 1) *
          ((P.n : ℚ) + 1) ^ (2 * (M - 1) + M + 1) *
            (2 : ℚ) ^ (∑ a : Fin M, P.length a) := by
  unfold actualValueMajorant actualLocalMajorant
  rw [pow_succ]
  ring

end OddPiPowers
