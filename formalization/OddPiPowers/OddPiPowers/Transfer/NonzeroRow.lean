module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! An invertible coefficient matrix has a row nonzero at each point. -/

@[expose] public section

namespace OddPiPowers

open Finset
open Polynomial
open scoped Matrix

theorem exists_nonzero_row (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hA : A.det ≠ 0) (y : ℂ) :
    ∃ i, (∑ j, A i j * y ^ (j : ℕ)) ≠ 0 := by
  by_contra h
  have hrow : ∀ i, (∑ j, A i j * y ^ (j : ℕ)) = 0 := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hv : A *ᵥ (fun j => y ^ (j : ℕ)) = 0 := by
    ext i
    simpa [Matrix.mulVec, dotProduct] using hrow i
  have hv' := Matrix.eq_zero_of_mulVec_eq_zero hA hv
  have hzero := congrFun hv' ⟨0, Nat.succ_pos m⟩
  simp at hzero

/-- The coefficient matrix of a finite family of polynomials of degree at
most `m`. -/
def coefficientMatrix (m : ℕ) (U : Fin (m + 1) → GaussianInt[X]) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) GaussianInt :=
  fun i j => (U i).coeff j

theorem eval₂_eq_coeff_sum (m : ℕ) (p : GaussianInt[X]) (hp : p.natDegree ≤ m) (y : ℂ) :
    p.eval₂ GaussianInt.toComplex y =
      ∑ j : Fin (m + 1), ((p.coeff j : GaussianInt) : ℂ) * y ^ (j : ℕ) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)]
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => ((p.coeff j : GaussianInt) : ℂ) * y ^ j)
    (m + 1)).symm

/-- A nonzero Gaussian determinant selects a polynomial nonzero at any chosen
complex point; the row is allowed to depend on that point. -/
theorem exists_polynomial_nonzero_row (m : ℕ) (U : Fin (m + 1) → GaussianInt[X])
    (hdeg : ∀ i, (U i).natDegree ≤ m) (hdet : (coefficientMatrix m U).det ≠ 0) (y : ℂ) :
    ∃ i, (U i).eval₂ GaussianInt.toComplex y ≠ 0 := by
  let A := coefficientMatrix m U
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := GaussianInt.toComplex.mapMatrix A
  have hdetB : B.det ≠ 0 := by
    have hmap : GaussianInt.toComplex A.det ≠ 0 := by
      intro hzero
      apply hdet
      exact GaussianInt.toComplex_eq_zero.mp hzero
    simpa only [B, RingHom.map_det] using hmap
  obtain ⟨i, hi⟩ := exists_nonzero_row m B hdetB y
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  change (∑ j : Fin (m + 1), (((U i).coeff j : GaussianInt) : ℂ) * y ^ (j : ℕ)) = 0
  exact (eval₂_eq_coeff_sum m (U i) (hdeg i) y).symm.trans hz

end OddPiPowers
