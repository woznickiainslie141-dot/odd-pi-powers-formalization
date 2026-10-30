module

public import OddPiPowers.Transfer.AuxiliaryFamily
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Uniform disk and divided-difference estimates from bounded coefficients. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators

theorem polynomial_eval_disk_bound (p : Polynomial ℂ) (m : ℕ) (hp : p.natDegree ≤ m)
    (H : ℝ) (hH : 0 ≤ H) (hc : ∀ j ≤ m, ‖p.coeff j‖ ≤ H)
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖p.eval z‖ ≤ ((m + 1 : ℕ) : ℝ) * H * (2 : ℝ) ^ m := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), ‖p.coeff j * z ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), H * (2 : ℝ) ^ m := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hc j hjm)
        ((pow_le_pow_left₀ (norm_nonneg _) hz j).trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjm))
        (by positivity) hH
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem dividedDifference_eval_disk_bound (m : ℕ) (u : ℕ → ℂ)
    (H : ℝ) (hH : 0 ≤ H) (hu : ∀ j ≤ m, ‖u j‖ ≤ H)
    (x z : ℂ) (hx : ‖x‖ ≤ 2) (hz : ‖z‖ ≤ 2) :
    ‖(dividedDifference m u x).eval z‖ ≤
      ((m + 1 : ℕ) : ℝ) ^ 2 * H * (2 : ℝ) ^ m := by
  simp only [dividedDifference, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1),
        ‖u j * ∑ a ∈ Finset.range j, x ^ a * z ^ (j - 1 - a)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), H * (((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ m) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      rw [norm_mul]
      apply mul_le_mul (hu j hjm) ?_ (norm_nonneg _) hH
      calc
        _ ≤ ∑ a ∈ Finset.range j, ‖x ^ a * z ^ (j - 1 - a)‖ := norm_sum_le _ _
        _ ≤ ∑ a ∈ Finset.range j, (2 : ℝ) ^ m := by
          apply Finset.sum_le_sum
          intro a ha
          have haj : a < j := Finset.mem_range.mp ha
          rw [norm_mul, norm_pow, norm_pow]
          calc
            _ ≤ (2 : ℝ) ^ a * (2 : ℝ) ^ (j - 1 - a) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx a)
                (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity) (by positivity)
            _ = (2 : ℝ) ^ (j - 1) := by rw [← pow_add]; congr 1; omega
            _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
        _ = (j : ℝ) * (2 : ℝ) ^ m := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show j ≤ m + 1 by omega)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem norm_lambda_le_two : ‖lambda‖ ≤ 2 := by
  unfold lambda
  rw [norm_div, norm_mul, Complex.norm_I, one_mul]
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hp]
  norm_num
  linarith [Real.pi_lt_four]

end OddPiPowers
