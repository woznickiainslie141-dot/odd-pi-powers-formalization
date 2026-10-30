module

public import OddPiPowers.Transfer.Comparison
public import OddPiPowers.Foundations.ExponentUpperBound
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Positive real roots and the distance comparison for powers of π. -/

@[expose] public section

namespace OddPiPowers

open Finset

theorem exists_positive_nth_root (a : ℝ) (ha : 0 < a) (k : ℕ) (hk : 0 < k) :
    ∃ θ : ℝ, 0 < θ ∧ θ ^ k = a := by
  refine ⟨a ^ ((k : ℝ)⁻¹), Real.rpow_pos_of_pos ha _, ?_⟩
  exact Real.rpow_inv_natCast_pow ha.le (Nat.ne_of_gt hk)

theorem lambda_distance (θ : ℝ) :
    ‖lambda - Complex.I * (θ : ℂ) / 2‖ = |Real.pi - θ| / 2 := by
  have heq : lambda - Complex.I * (θ : ℂ) / 2 =
      Complex.I * ((Real.pi - θ : ℝ) : ℂ) / 2 := by
    simp only [lambda, Complex.ofReal_sub]
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_two]

/-- A fixed positive cutoff, depending only on `k`, keeps the chosen real
root in the disk needed for the uniform height estimate. -/
theorem pi_power_cutoff_pos (k : ℕ) (hk : 0 < k) :
    0 < ((4 : ℝ) ^ k - Real.pi ^ k) / 2 := by
  have hpow : Real.pi ^ k < (4 : ℝ) ^ k :=
    pow_lt_pow_left₀ Real.pi_lt_four Real.pi_nonneg (Nat.ne_of_gt hk)
  linarith

theorem root_in_disk_of_close (k : ℕ) (hk : 0 < k) (θ : ℝ) (hθ : 0 ≤ θ)
    (hclose : |Real.pi ^ k - θ ^ k| < ((4 : ℝ) ^ k - Real.pi ^ k) / 2) :
    ‖Complex.I * (θ : ℂ) / 2‖ ≤ 2 := by
  have hcut := pi_power_cutoff_pos k hk
  have hθpow : θ ^ k < (4 : ℝ) ^ k := by
    have habs := (abs_lt.mp hclose).1
    linarith
  have hθlt : θ < 4 := lt_of_pow_lt_pow_left₀ k (by norm_num) hθpow
  have hnorm : ‖Complex.I * (θ : ℂ) / 2‖ = θ / 2 := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hθ, Complex.norm_two]
  rw [hnorm]
  linarith

/-- Factoring the difference of powers transfers the distance from the
positive real root back to the target power. -/
theorem pi_power_distance_lower (k : ℕ) (hk : 0 < k) (θ : ℝ) (hθ : 0 ≤ θ) :
    2 * Real.pi ^ (k - 1) * ‖lambda - Complex.I * (θ : ℂ) / 2‖ ≤
      |Real.pi ^ k - θ ^ k| := by
  let S : ℝ := ∑ i ∈ range k, θ ^ i * Real.pi ^ (k - 1 - i)
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg hθ _) (pow_nonneg Real.pi_nonneg _)
  have hsum : Real.pi ^ (k - 1) ≤ S := by
    have h := Finset.single_le_sum (s := range k)
      (f := fun i : ℕ => θ ^ i * Real.pi ^ (k - 1 - i))
      (fun i hi => mul_nonneg (pow_nonneg hθ _) (pow_nonneg Real.pi_nonneg _))
      (show 0 ∈ range k from mem_range.mpr hk)
    simpa only [pow_zero, one_mul, Nat.sub_zero, S] using h
  have hid : θ ^ k - Real.pi ^ k = (θ - Real.pi) * S := by
    simpa only [S, mul_comm] using (geom_sum₂_mul θ Real.pi k).symm
  calc
    2 * Real.pi ^ (k - 1) * ‖lambda - Complex.I * (θ : ℂ) / 2‖ =
        |θ - Real.pi| * Real.pi ^ (k - 1) := by
      rw [lambda_distance, abs_sub_comm θ Real.pi]
      ring
    _ ≤ |θ - Real.pi| * S := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |Real.pi ^ k - θ ^ k| := by
      rw [← abs_of_nonneg hS, ← abs_mul, ← hid, abs_sub_comm]

end OddPiPowers
