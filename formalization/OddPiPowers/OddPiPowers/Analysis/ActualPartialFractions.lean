module

public import OddPiPowers.Construction.ActualAuxiliary
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp

/-! The actual polynomial numerator identity, evaluated as a meromorphic
partial-fraction identity. The interval factorials occur exactly once. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

open Polynomial

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def denominatorValue (z : ℂ) : ℂ :=
  P.denominator.eval₂ (Rat.castHom ℂ) z

noncomputable def intervalFactorialProduct : ℂ :=
  ∏ a : Fin M, (Nat.factorial (P.length a) : ℂ)

noncomputable def factorialRationalKernel (h : ℕ) (z : ℂ) : ℂ :=
  P.intervalFactorialProduct * z ^ h / P.denominatorValue z

theorem denominator_factor_at_pole (pole : ℕ) (hpole : pole ≤ P.n) :
    P.denominator = (X + C (pole : ℚ)) ^ P.multiplicity pole *
      P.otherRootProduct pole := by
  classical
  have hp : pole ∈ Finset.range (P.n + 1) := by simp [hpole]
  rw [P.denominator_eq_rootProduct, otherRootProduct]
  have hprod : (∏ r ∈ Finset.range (P.n + 1),
      (if r = pole then (X + C (r : ℚ)) ^ P.multiplicity r else 1) *
      (if r = pole then 1 else (X + C (r : ℚ)) ^ P.multiplicity r)) =
        ∏ r ∈ Finset.range (P.n + 1), (X + C (r : ℚ)) ^ P.multiplicity r := by
    apply Finset.prod_congr rfl
    intro r hr
    by_cases he : r = pole <;> simp [he]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', ite_eq_left hp] at hprod
  exact hprod.symm

theorem denominatorValue_ne_zero_of_nonpoles (z : ℂ)
    (hz : ∀ r : ℕ, r ≤ P.n → z + (r : ℂ) ≠ 0) : P.denominatorValue z ≠ 0 := by
  classical
  simp only [denominatorValue, P.denominator_eq_rootProduct,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.C_eq_natCast,
    Polynomial.eval₂_natCast]
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  exact pow_ne_zero _ (hz r (by have := Finset.mem_range.mp hr; omega))

theorem partialFractionTerm_div_denominator (h pole q : ℕ)
    (hpole : pole ≤ P.n) (hq : q < P.multiplicity pole) (z : ℂ)
    (hz : z + (pole : ℂ) ≠ 0) (hQ : P.denominatorValue z ≠ 0) :
    (P.partialFractionTerm h pole q).eval₂ (Rat.castHom ℂ) z / P.denominatorValue z =
      ((PowerSeries.coeff q (P.localExpansion pole h) : ℚ) : ℂ) /
        (z + (pole : ℂ)) ^ (P.multiplicity pole - q) := by
  have he := congrArg (fun p : Polynomial ℚ => p.eval₂ (Rat.castHom ℂ) z)
    (P.denominator_factor_at_pole pole hpole)
  change P.denominatorValue z = _ at he
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.C_eq_natCast, Polynomial.eval₂_natCast] at he
  have hother : (P.otherRootProduct pole).eval₂ (Rat.castHom ℂ) z ≠ 0 := by
    intro hzero
    apply hQ
    rw [he, hzero, mul_zero]
  have hmu : P.multiplicity pole = q + (P.multiplicity pole - q) := by omega
  rw [he, hmu, pow_add]
  simp only [partialFractionTerm, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.C_eq_natCast, Polynomial.eval₂_natCast]
  field_simp
  simp only [Nat.add_sub_cancel_left, Rat.coe_castHom, mul_comm]

/-- No residue assumption: this follows from the already proved actual
polynomial identity by evaluation and division at a nonpole. -/
theorem factorialRationalKernel_partialFractions (h : Fin M) (hM : 0 < M)
    (z : ℂ) (hz : ∀ r : ℕ, r ≤ P.n → z + (r : ℂ) ≠ 0) :
    P.factorialRationalKernel h.val z =
      ∑ pole ∈ Finset.range (P.n + 1), ∑ q ∈ Finset.range (P.multiplicity pole),
        ((PowerSeries.coeff q (P.localExpansion pole h.val) : ℚ) : ℂ) /
          (z + (pole : ℂ)) ^ (P.multiplicity pole - q) := by
  classical
  have hQ := P.denominatorValue_ne_zero_of_nonpoles z hz
  have he := congrArg (fun p : Polynomial ℚ => p.eval₂ (Rat.castHom ℂ) z)
    (P.partialFractionNumerator_eq h hM)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at he
  simp only [map_prod, map_natCast] at he
  change (P.partialFractionNumerator h.val).eval₂ (Rat.castHom ℂ) z =
    P.intervalFactorialProduct * z ^ h.val at he
  rw [factorialRationalKernel, ← he]
  simp only [partialFractionNumerator, Polynomial.eval₂_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro pole hpole
  apply Finset.sum_congr rfl
  intro q hq
  exact P.partialFractionTerm_div_denominator h.val pole q
    (by have := Finset.mem_range.mp hpole; omega) (Finset.mem_range.mp hq) z
    (hz pole (by have := Finset.mem_range.mp hpole; omega)) hQ

end OddPiPowers.ActualIntervals
