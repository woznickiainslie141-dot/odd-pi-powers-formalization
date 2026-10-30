module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Tactic.Ring

/-! A finite divided difference, valid even when the two points coincide. -/

@[expose] public section

namespace OddPiPowers

open Finset Polynomial

variable {R : Type*} [CommRing R]

/-- A polynomial given by a finite coefficient vector. -/
noncomputable def coefficientPolynomial (m : ℕ) (u : ℕ → R) : R[X] :=
  ∑ j ∈ range (m + 1), C (u j) * X ^ j

/-- The divided difference with the first argument fixed. Its coefficients
belong to the ambient ring, which will be `ℂ` in the transfer theorem. -/
noncomputable def dividedDifference (m : ℕ) (u : ℕ → R) (x : R) : R[X] :=
  ∑ j ∈ range (m + 1), C (u j) *
    ∑ a ∈ range j, C (x ^ a) * X ^ (j - 1 - a)

theorem coefficientPolynomial_eval_sub (m : ℕ) (u : ℕ → R) (x y : R) :
    (coefficientPolynomial m u).eval x - (coefficientPolynomial m u).eval y =
      (x - y) * (dividedDifference m u x).eval y := by
  simp only [coefficientPolynomial, dividedDifference, eval_finsetSum, eval_mul,
    eval_C, eval_pow, eval_X]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_sub, ← geom_sum₂_mul x y j]
  ring

/-- The same identity for any polynomial of the indicated degree. -/
theorem polynomial_eval_sub (p : R[X]) (m : ℕ) (hm : p.natDegree ≤ m) (x y : R) :
    p.eval x - p.eval y =
      (x - y) * (dividedDifference m p.coeff x).eval y := by
  have hp : coefficientPolynomial m p.coeff = p := by
    simpa only [coefficientPolynomial] using
      (p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hm)).symm
  simpa only [hp] using coefficientPolynomial_eval_sub m p.coeff x y

end OddPiPowers
