module

public import OddPiPowers.Analysis.ActualHeightRate
public import OddPiPowers.Analysis.BalancedDiskHeight
public import OddPiPowers.Construction.ReducedGaussianRows

/-! Uniform disk heights for the actual integral coefficient quotient. -/

@[expose] public section

namespace OddPiPowers

open Polynomial Filter
open scoped Topology

noncomputable def actualReducedHeight {M : ℕ} (P : ActualIntervals M) : ℝ :=
  ((actualValueMajorant P : ℚ) : ℝ) / (P.actualAuxiliaryPrimeDivisor : ℝ)

theorem actualReducedHeight_nonneg {M : ℕ} (P : ActualIntervals M) :
    0 ≤ actualReducedHeight P := by
  unfold actualReducedHeight
  exact div_nonneg (by exact_mod_cast (actualValueMajorant_pos P).le) (Nat.cast_nonneg _)

theorem reduced_complexPolynomial_degree (m : ℕ) (P : ActualIntervals (m + 1))
    (h : Fin (m + 1)) :
    (complexPolynomial (reducedGaussianRow P h)).natDegree ≤ m := by
  exact Polynomial.natDegree_map_le.trans (by simpa using reducedGaussianRow_degree P h)

theorem reduced_complexPolynomial_coeff_bound (m : ℕ) (P : ActualIntervals (m + 1))
    (h : Fin (m + 1)) (j : ℕ) (hj : j ≤ m) :
    ‖(complexPolynomial (reducedGaussianRow P h)).coeff j‖ ≤ actualReducedHeight P := by
  let k : Fin (m + 1) := ⟨j, by omega⟩
  simp only [complexPolynomial, Polynomial.coeff_map]
  change ‖GaussianInt.toComplex ((finiteGaussianRow (reducedGaussianMatrix P h)).coeff k.val)‖ ≤ _
  rw [finiteGaussianRow_coeff]
  change ‖GaussianInt.toComplex (reducedGaussianCoefficient P h k)‖ ≤ _
  rw [reducedGaussianCoefficient_norm]
  exact div_le_div_of_nonneg_right (actualAuxiliary_evalI_height P h k) (Nat.cast_nonneg _)

theorem reduced_row_disk_bound (m : ℕ) (P : ActualIntervals (m + 1))
    (h : Fin (m + 1)) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖(complexPolynomial (reducedGaussianRow P h)).eval z‖ ≤
      balancedDiskConstant m * actualReducedHeight P := by
  have hV := actualReducedHeight_nonneg P
  have ht := polynomial_eval_disk_bound _ m (reduced_complexPolynomial_degree m P h)
    _ (actualReducedHeight_nonneg P) (reduced_complexPolynomial_coeff_bound m P h) z hz
  have hM : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hsq : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ ((m + 1 : ℕ) : ℝ) * actualReducedHeight P * 2 ^ m := ht
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * actualReducedHeight P * 2 ^ m := by
      gcongr
    _ = _ := by unfold balancedDiskConstant; ring

theorem reduced_difference_disk_bound (m : ℕ) (P : ActualIntervals (m + 1))
    (h : Fin (m + 1)) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖(complexDividedDifference m (reducedGaussianRow P h)).eval z‖ ≤
      balancedDiskConstant m * actualReducedHeight P := by
  have ht := dividedDifference_eval_disk_bound m
    (complexPolynomial (reducedGaussianRow P h)).coeff _ (actualReducedHeight_nonneg P)
    (reduced_complexPolynomial_coeff_bound m P h) lambda z norm_lambda_le_two hz
  exact ht.trans_eq (by unfold balancedDiskConstant; ring)

end OddPiPowers
