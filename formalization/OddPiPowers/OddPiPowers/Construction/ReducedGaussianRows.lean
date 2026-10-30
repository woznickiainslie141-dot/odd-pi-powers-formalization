module

public import OddPiPowers.Construction.FiniteGaussianRows
public import OddPiPowers.Analysis.ReducedCentralBound

/-! Actual reduced Gaussian rows; the divisor and nonsingularity are the accepted ones. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def reducedGaussianCoefficient (h j : Fin M) : GaussianInt :=
  (P.reducedAuxiliaryInt h j).eval₂ (Int.castRingHom GaussianInt) gaussianI

noncomputable def reducedGaussianMatrix : Matrix (Fin M) (Fin M) GaussianInt :=
  fun h j => reducedGaussianCoefficient P h j

noncomputable def reducedGaussianRow (h : Fin M) : Polynomial GaussianInt :=
  finiteGaussianRow (reducedGaussianMatrix P h)

theorem reducedGaussianCoefficient_complex (h j : Fin M) :
    GaussianInt.toComplex (reducedGaussianCoefficient P h j) =
      P.reducedAuxiliaryIntMatrixAtI h j := by
  exact gaussianIntegerPolynomial_eval_toComplex (P.reducedAuxiliaryInt h j)

theorem reducedGaussianMatrix_complex :
    GaussianInt.toComplex.mapMatrix (reducedGaussianMatrix P) = P.reducedAuxiliaryIntMatrixAtI := by
  funext h j
  exact reducedGaussianCoefficient_complex P h j

theorem reducedGaussianMatrix_det_ne_zero : (reducedGaussianMatrix P).det ≠ 0 := by
  intro hz
  have he := GaussianInt.toComplex.map_det (reducedGaussianMatrix P)
  rw [hz, map_zero, reducedGaussianMatrix_complex] at he
  exact P.reducedAuxiliaryIntMatrixAtI_det_ne_zero he.symm

theorem reducedGaussianRow_eval (h : Fin M) (z : ℂ) :
    (reducedGaussianRow P h).eval₂ GaussianInt.toComplex z = P.reducedAuxiliaryRow h z := by
  simp only [reducedGaussianRow, finiteGaussianRow_eval, reducedGaussianMatrix,
    reducedGaussianCoefficient_complex, ActualIntervals.reducedAuxiliaryRow]

set_option backward.isDefEq.respectTransparency false in
theorem reducedGaussianCoefficient_norm (h j : Fin M) :
    ‖GaussianInt.toComplex (reducedGaussianCoefficient P h j)‖ =
      ‖(actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I‖ /
        (P.actualAuxiliaryPrimeDivisor : ℝ) := by
  rw [reducedGaussianCoefficient_complex]
  have he := congrFun (congrFun P.reducedAuxiliaryIntMatrixAtI_smul h) j
  have he' : (P.actualAuxiliaryPrimeDivisor : ℂ) * P.reducedAuxiliaryIntMatrixAtI h j =
      (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I := by
    simpa only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_natCast,
      actualAuxiliaryPolynomialMatrixAtI, RingHom.mapMatrix_apply,
      actualAuxiliaryPolynomialEvalI, Polynomial.coe_eval₂RingHom,
      Matrix.map_apply, actualAuxiliaryPolynomialMatrix] using he
  have hn := congrArg norm he'
  rw [norm_mul, Complex.norm_natCast] at hn
  have hD : (P.actualAuxiliaryPrimeDivisor : ℝ) ≠ 0 := by
    exact_mod_cast P.actualAuxiliaryPrimeDivisor_pos.ne'
  exact (eq_div_iff hD).mpr ((mul_comm _ _).trans hn)

theorem reducedGaussianRow_degree (h : Fin M) : (reducedGaussianRow P h).natDegree ≤ M - 1 :=
  finiteGaussianRow_degree _

theorem reducedGaussianRow_matrix_det (m : ℕ) (P : ActualIntervals (m + 1)) :
    (coefficientMatrix m (reducedGaussianRow P)).det ≠ 0 := by
  have he : reducedGaussianRow P = fun h => finiteGaussianRow (reducedGaussianMatrix P h) := by
    funext h
    rfl
  rw [he, finiteGaussianRow_coefficientMatrix]
  exact reducedGaussianMatrix_det_ne_zero P

end OddPiPowers
