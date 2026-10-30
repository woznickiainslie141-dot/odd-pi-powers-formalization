module

public import OddPiPowers.Arithmetic.ReducedAuxiliary
public import OddPiPowers.Foundations.GaussianArithmetic
public import OddPiPowers.Transfer.NonzeroRow
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Unreduced Gaussian rows from the actual auxiliary family. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators

variable {M : ℕ}

/-- Evaluate each actual integer auxiliary polynomial at the Gaussian `i`. -/
noncomputable def gaussianAuxiliaryCoefficient (P : ActualIntervals M)
    (h j : Fin M) : GaussianInt :=
  (actualAuxiliaryInt P h j).eval₂ (Int.castRingHom GaussianInt) gaussianI

theorem gaussianAuxiliaryCoefficient_toComplex (P : ActualIntervals M)
    (h j : Fin M) :
    GaussianInt.toComplex (gaussianAuxiliaryCoefficient P h j) =
      (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I := by
  have heval := Polynomial.hom_eval₂ (actualAuxiliaryInt P h j)
    (Int.castRingHom GaussianInt) GaussianInt.toComplex gaussianI
  have hcomp : GaussianInt.toComplex.comp (Int.castRingHom GaussianInt) =
      Int.castRingHom ℂ := by ext z; simp
  rw [hcomp] at heval
  have heval' : GaussianInt.toComplex (gaussianAuxiliaryCoefficient P h j) =
      ActualIntervals.actualAuxiliaryIntEvalI (actualAuxiliaryInt P h j) := by
    simpa only [gaussianAuxiliaryCoefficient, ActualIntervals.actualAuxiliaryIntEvalI,
      Polynomial.coe_eval₂RingHom, gaussianI_toComplex] using heval
  simpa [actualAuxiliaryPolynomialEvalI] using
    heval'.trans (P.actualAuxiliaryInt_evalI h j)

/-- The row polynomial has coefficient `j` equal to the actual value at `i`. -/
noncomputable def gaussianAuxiliaryRow (P : ActualIntervals M)
    (h : Fin M) : Polynomial GaussianInt :=
  ∑ j : Fin M, C (gaussianAuxiliaryCoefficient P h j) * X ^ j.val

theorem gaussianAuxiliaryRow_coeff (P : ActualIntervals M) (h j : Fin M) :
    (gaussianAuxiliaryRow P h).coeff j.val = gaussianAuxiliaryCoefficient P h j := by
  classical
  rw [gaussianAuxiliaryRow, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    have hne : j.val ≠ k.val := by
      intro hv
      exact hkj (Fin.ext hv.symm)
    simp [hne]
  · simp

theorem gaussianAuxiliaryRow_natDegree_le (P : ActualIntervals M) (h : Fin M) :
    (gaussianAuxiliaryRow P h).natDegree ≤ M - 1 := by
  classical
  rw [gaussianAuxiliaryRow]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  calc
    _ ≤ (X ^ j.val : Polynomial GaussianInt).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ j.val := by simp
    _ ≤ M - 1 := by omega

theorem gaussianAuxiliaryRow_eval (P : ActualIntervals M) (h : Fin M) (z : ℂ) :
    (gaussianAuxiliaryRow P h).eval₂ GaussianInt.toComplex z =
      ∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * z ^ j.val := by
  simp only [gaussianAuxiliaryRow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    gaussianAuxiliaryCoefficient_toComplex]

noncomputable def gaussianAuxiliaryCoefficientMatrix (P : ActualIntervals M) :
    Matrix (Fin M) (Fin M) GaussianInt :=
  fun h j => (gaussianAuxiliaryRow P h).coeff j.val

theorem gaussianAuxiliaryCoefficientMatrix_complex (P : ActualIntervals M) :
    GaussianInt.toComplex.mapMatrix (gaussianAuxiliaryCoefficientMatrix P) =
      actualAuxiliaryPolynomialMatrixAtI P := by
  ext h j
  simpa [gaussianAuxiliaryCoefficientMatrix, gaussianAuxiliaryRow_coeff, actualAuxiliaryPolynomialMatrixAtI,
    actualAuxiliaryPolynomialMatrix, actualAuxiliaryPolynomialEvalI] using
      gaussianAuxiliaryCoefficient_toComplex P h j

theorem gaussianAuxiliaryCoefficientMatrix_det_ne_zero (P : ActualIntervals M) :
    (gaussianAuxiliaryCoefficientMatrix P).det ≠ 0 := by
  intro hz
  have hm : (GaussianInt.toComplex.mapMatrix (gaussianAuxiliaryCoefficientMatrix P)).det = 0 := by
    have he := GaussianInt.toComplex.map_det (gaussianAuxiliaryCoefficientMatrix P)
    rw [hz, map_zero] at he
    exact he.symm
  rw [gaussianAuxiliaryCoefficientMatrix_complex] at hm
  exact actualAuxiliaryPolynomialMatrixAtI_det_ne_zero P hm

/- The exact matrix interface used in `AuxiliaryFamily` for `M = m + 1`. -/
set_option backward.isDefEq.respectTransparency false in
theorem gaussianAuxiliaryRow_coefficientMatrix_det_ne_zero (m : ℕ)
    (P : ActualIntervals (m + 1)) :
    (coefficientMatrix m (gaussianAuxiliaryRow P)).det ≠ 0 := by
  change (gaussianAuxiliaryCoefficientMatrix P).det ≠ 0
  exact gaussianAuxiliaryCoefficientMatrix_det_ne_zero P

theorem gaussianAuxiliaryRow_degree_for_transfer (m : ℕ)
    (P : ActualIntervals (m + 1)) (h : Fin (m + 1)) :
    (gaussianAuxiliaryRow P h).natDegree ≤ m := by
  simpa using gaussianAuxiliaryRow_natDegree_le P h

end OddPiPowers
