module

public import OddPiPowers.Construction.GaussianAuxiliaryRows

/-! A finite Gaussian coefficient vector, with exact degree and matrix interfaces. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators

variable {M : ℕ}

noncomputable def finiteGaussianRow (a : Fin M → GaussianInt) : Polynomial GaussianInt :=
  ∑ j : Fin M, C (a j) * X ^ j.val

theorem finiteGaussianRow_coeff (a : Fin M → GaussianInt) (j : Fin M) :
    (finiteGaussianRow a).coeff j.val = a j := by
  classical
  rw [finiteGaussianRow, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    have hne : j.val ≠ k.val := by intro hv; exact hkj (Fin.ext hv.symm)
    simp [hne]
  · simp

theorem finiteGaussianRow_degree (a : Fin M → GaussianInt) :
    (finiteGaussianRow a).natDegree ≤ M - 1 := by
  classical
  rw [finiteGaussianRow]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  calc
    _ ≤ (X ^ j.val : Polynomial GaussianInt).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ j.val := by simp
    _ ≤ M - 1 := by omega

theorem finiteGaussianRow_eval (a : Fin M → GaussianInt) (z : ℂ) :
    (finiteGaussianRow a).eval₂ GaussianInt.toComplex z =
      ∑ j : Fin M, GaussianInt.toComplex (a j) * z ^ j.val := by
  simp only [finiteGaussianRow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]

theorem finiteGaussianRow_coefficientMatrix (m : ℕ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) GaussianInt) :
    coefficientMatrix m (fun h => finiteGaussianRow (A h)) = A := by
  funext h j
  exact finiteGaussianRow_coeff (A h) j

theorem gaussianIntegerPolynomial_eval_toComplex (p : Polynomial ℤ) :
    GaussianInt.toComplex (p.eval₂ (Int.castRingHom GaussianInt) gaussianI) =
      ActualIntervals.actualAuxiliaryIntEvalI p := by
  have he := Polynomial.hom_eval₂ p (Int.castRingHom GaussianInt) GaussianInt.toComplex gaussianI
  have hcomp : GaussianInt.toComplex.comp (Int.castRingHom GaussianInt) = Int.castRingHom ℂ := by
    ext z
    simp
  rw [hcomp] at he
  simpa only [ActualIntervals.actualAuxiliaryIntEvalI, Polynomial.coe_eval₂RingHom,
    gaussianI_toComplex] using he

end OddPiPowers
