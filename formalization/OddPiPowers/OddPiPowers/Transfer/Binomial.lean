module

public import OddPiPowers.Transfer.AlgebraicValue

/-! The roots of a binomial with nonzero leading coefficient have the same
modulus, without assuming that the binomial is irreducible. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

noncomputable def gaussianBinomial (a b : GaussianInt) (k : ℕ) : GaussianInt[X] :=
  C a * X ^ k - C b

theorem gaussianBinomial_natDegree (a b : GaussianInt) (k : ℕ)
    (ha : a ≠ 0) (hk : 0 < k) : (gaussianBinomial a b k).natDegree = k := by
  have hlt : (C b : GaussianInt[X]).natDegree < (C a * X ^ k).natDegree := by
    rw [natDegree_C, natDegree_C_mul_X_pow k a ha]
    exact hk
  rw [gaussianBinomial, natDegree_sub_eq_left_of_natDegree_lt hlt,
    natDegree_C_mul_X_pow k a ha]

theorem gaussianBinomial_leadingCoeff (a b : GaussianInt) (k : ℕ)
    (ha : a ≠ 0) (hk : 0 < k) : (gaussianBinomial a b k).leadingCoeff = a := by
  rw [leadingCoeff, gaussianBinomial_natDegree a b k ha hk, gaussianBinomial, coeff_sub,
    coeff_C_mul_X_pow, coeff_C_of_ne_zero (Nat.ne_of_gt hk)]
  simp

theorem gaussianBinomial_ne_zero (a b : GaussianInt) (k : ℕ)
    (ha : a ≠ 0) (hk : 0 < k) : gaussianBinomial a b k ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  simpa only [gaussianBinomial_leadingCoeff a b k ha hk] using ha

theorem gaussianBinomial_roots_norm (a b : GaussianInt) (k : ℕ)
    (ha : a ≠ 0) (hk : 0 < k) (y z : ℂ)
    (hy : (gaussianBinomial a b k).eval₂ GaussianInt.toComplex y = 0)
    (hz : (gaussianBinomial a b k).eval₂ GaussianInt.toComplex z = 0) : ‖z‖ = ‖y‖ := by
  have haC : (a : ℂ) ≠ 0 := fun h => ha (GaussianInt.toComplex_eq_zero.mp h)
  have hy' : (a : ℂ) * y ^ k = (b : ℂ) := by
    apply sub_eq_zero.mp
    simpa [gaussianBinomial] using hy
  have hz' : (a : ℂ) * z ^ k = (b : ℂ) := by
    apply sub_eq_zero.mp
    simpa [gaussianBinomial] using hz
  have hp : z ^ k = y ^ k := mul_left_cancel₀ haC (hz'.trans hy'.symm)
  apply (pow_left_inj₀ (norm_nonneg z) (norm_nonneg y) (Nat.ne_of_gt hk)).mp
  simpa only [norm_pow] using congrArg norm hp

/-- The binomial is only an annihilator; the proof uses the primitive minimal
polynomial even when the binomial is reducible. -/
theorem gaussian_binomial_value_lower_bound (a b : GaussianInt) (k : ℕ)
    (ha : a ≠ 0) (hk : 0 < k) (y : ℂ)
    (hy : (gaussianBinomial a b k).eval₂ GaussianInt.toComplex y = 0) (hyDisk : ‖y‖ ≤ 2)
    (U : GaussianInt[X]) (hU : U.eval₂ GaussianInt.toComplex y ≠ 0)
    (m : ℕ) (hUdegree : U.natDegree ≤ m)
    (B H : NNReal) (hB : 1 ≤ B) (hH : 1 ≤ H) (haB : ‖(a : ℂ)‖₊ ≤ B)
    (hheight : ∀ z : ℂ, ‖z‖ ≤ 2 → ‖(U.map GaussianInt.toComplex).eval z‖₊ ≤ H) :
    1 / (B ^ m * H ^ (k - 1)) ≤ ‖(U.map GaussianInt.toComplex).eval y‖₊ := by
  apply gaussian_algebraic_value_lower_bound (gaussianBinomial a b k) U y
    (gaussianBinomial_ne_zero a b k ha hk) hy hU m k
  · rw [gaussianBinomial_natDegree a b k ha hk]
  · exact hUdegree
  · exact hB
  · exact hH
  · simpa only [gaussianBinomial_leadingCoeff a b k ha hk] using haB
  · intro z hz
    rw [gaussianBinomial_roots_norm a b k ha hk y z hy hz]
    exact hyDisk
  · exact hheight

end OddPiPowers
