module

public import OddPiPowers.Analysis.PolynomialDiskHeight
public import OddPiPowers.Analysis.BalancedHeightRate
public import OddPiPowers.Construction.GaussianAuxiliaryRows

/-! Actual Gaussian rows have uniform disk and divided-difference heights. -/

@[expose] public section

namespace OddPiPowers

open Polynomial Filter
open scoped Topology

noncomputable def balancedGaussianRows (m n : ℕ) (h : Fin (m + 1)) : Polynomial GaussianInt :=
  gaussianAuxiliaryRow (balancedActualFamily (m + 1) n) h

noncomputable def balancedDiskConstant (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ m

theorem balancedDiskConstant_pos (m : ℕ) : 0 < balancedDiskConstant m := by
  unfold balancedDiskConstant
  positivity

theorem balanced_complexPolynomial_degree (m n : ℕ) (h : Fin (m + 1)) :
    (complexPolynomial (balancedGaussianRows m n h)).natDegree ≤ m := by
  exact Polynomial.natDegree_map_le.trans
    (gaussianAuxiliaryRow_degree_for_transfer m (balancedActualFamily (m + 1) n) h)

theorem balanced_complexPolynomial_coeff_bound (m n : ℕ) (h : Fin (m + 1))
    (j : ℕ) (hj : j ≤ m) :
    ‖(complexPolynomial (balancedGaussianRows m n h)).coeff j‖ ≤
      ((balancedValueMajorant (m + 1) n : ℚ) : ℝ) := by
  let k : Fin (m + 1) := ⟨j, by omega⟩
  simp only [complexPolynomial, balancedGaussianRows, Polynomial.coeff_map]
  change ‖GaussianInt.toComplex ((gaussianAuxiliaryRow
    (balancedActualFamily (m + 1) n) h).coeff k.val)‖ ≤ _
  rw [gaussianAuxiliaryRow_coeff, gaussianAuxiliaryCoefficient_toComplex]
  exact balanced_actualAuxiliary_evalI_bound (m + 1) n h k

theorem balanced_row_disk_bound (m n : ℕ) (h : Fin (m + 1))
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖(complexPolynomial (balancedGaussianRows m n h)).eval z‖ ≤
      balancedDiskConstant m * ((balancedValueMajorant (m + 1) n : ℚ) : ℝ) := by
  have hV : (0 : ℝ) ≤ ((balancedValueMajorant (m + 1) n : ℚ) : ℝ) := by
    exact_mod_cast (balancedValueMajorant_pos (m + 1) n).le
  have ht := polynomial_eval_disk_bound _ m (balanced_complexPolynomial_degree m n h)
    _ hV (balanced_complexPolynomial_coeff_bound m n h) z hz
  have hM : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hsq : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ ((m + 1 : ℕ) : ℝ) * ((balancedValueMajorant (m + 1) n : ℚ) : ℝ) * 2 ^ m := ht
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * ((balancedValueMajorant (m + 1) n : ℚ) : ℝ) * 2 ^ m := by
      gcongr
    _ = _ := by unfold balancedDiskConstant; ring

theorem balanced_difference_disk_bound (m n : ℕ) (h : Fin (m + 1))
    (z : ℂ) (hz : ‖z‖ ≤ 2) :
    ‖(complexDividedDifference m (balancedGaussianRows m n h)).eval z‖ ≤
      balancedDiskConstant m * ((balancedValueMajorant (m + 1) n : ℚ) : ℝ) := by
  have hV : (0 : ℝ) ≤ ((balancedValueMajorant (m + 1) n : ℚ) : ℝ) := by
    exact_mod_cast (balancedValueMajorant_pos (m + 1) n).le
  have ht := dividedDifference_eval_disk_bound m
    (complexPolynomial (balancedGaussianRows m n h)).coeff _ hV
    (balanced_complexPolynomial_coeff_bound m n h) lambda z norm_lambda_le_two hz
  exact ht.trans_eq (by unfold balancedDiskConstant; ring)

theorem balanced_disk_heights_eventually (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (∀ h z, ‖z‖ ≤ 2 → ‖(complexPolynomial (balancedGaussianRows m n h)).eval z‖ ≤
        Real.exp (((m : ℝ) + ((m + 1 : ℕ) : ℝ) * Real.log 2 + η) * n)) ∧
      (∀ h z, ‖z‖ ≤ 2 → ‖(complexDividedDifference m (balancedGaussianRows m n h)).eval z‖ ≤
        Real.exp (((m : ℝ) + ((m + 1 : ℕ) : ℝ) * Real.log 2 + η) * n)) := by
  have ht := balancedConstantHeight_eventually_exp (m + 1) (balancedDiskConstant m)
    (balancedDiskConstant_pos m) hη
  simp only [Nat.add_sub_cancel_right] at ht
  filter_upwards [ht] with n hn
  exact ⟨fun h z hz => (balanced_row_disk_bound m n h z hz).trans hn,
    fun h z hz => (balanced_difference_disk_bound m n h z hz).trans hn⟩

end OddPiPowers
