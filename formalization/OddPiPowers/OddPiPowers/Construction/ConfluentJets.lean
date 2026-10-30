module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.Ring

/-! Repeated-node Taylor data: the algebraic nondegeneracy kernel. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators Matrix

variable {K : Type*} [Field K]

theorem pow_X_sub_C_dvd_iff_taylor (p : K[X]) (a : K) (r : ℕ) :
    (X - C a) ^ r ∣ p ↔ ∀ j < r, (p.taylor a).coeff j = 0 := by
  have ht : Polynomial.taylor a (X - C a) = X := by
    simp [Polynomial.taylor_apply]
  rw [← Polynomial.X_pow_dvd_iff]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q.taylor a, ?_⟩
    rw [hq, Polynomial.taylor_mul, Polynomial.taylor_pow, ht]
  · rintro ⟨q, hq⟩
    refine ⟨q.taylor (-a), ?_⟩
    have hh := congrArg (Polynomial.taylor (-a)) hq
    rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero,
      Polynomial.taylor_mul, Polynomial.taylor_pow] at hh
    have hX : Polynomial.taylor (-a) (X : K[X]) = X - C a := by
      simp [Polynomial.taylor_apply, sub_eq_add_neg]
    simpa only [hX] using hh

/-- Too many vanishing Taylor coefficients at distinct nodes force a
polynomial to be zero. Multiplicities need not be equal or positive. -/
theorem eq_zero_of_confluent_jets {ι : Type*} [Fintype ι] (a : ι → K)
    (ha : Function.Injective a) (r : ι → ℕ) (p : K[X])
    (hdegree : p.natDegree < ∑ i, r i)
    (hjets : ∀ i j, j < r i → (p.taylor (a i)).coeff j = 0) : p = 0 := by
  classical
  by_contra hp
  have hdiv : (∏ i, (X - C (a i)) ^ r i) ∣ p := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact (Polynomial.pairwise_coprime_X_sub_C ha hij).pow
    · intro i
      exact (pow_X_sub_C_dvd_iff_taylor p (a i) (r i)).2 (hjets i)
  have hdeg := Polynomial.natDegree_le_of_dvd hdiv hp
  have heq : (∏ i, (X - C (a i)) ^ r i).natDegree = ∑ i, r i := by
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
    · intro i _
      exact (Polynomial.monic_X_sub_C (a i)).pow (r i)
  rw [heq] at hdeg
  omega

/-- Multiplication by an arbitrary unit power series preserves the vanishing
of all coefficients below `r`. This handles the local factors B_alpha,
including coefficients above the polynomial degree. -/
theorem unit_mul_jets_iff (B f : PowerSeries K) (r : ℕ)
    (hB : PowerSeries.coeff 0 B ≠ 0) :
    (∀ j < r, PowerSeries.coeff j (B * f) = 0) ↔
      ∀ j < r, PowerSeries.coeff j f = 0 := by
  have hunit : IsUnit B := PowerSeries.isUnit_iff_constantCoeff.2
    (isUnit_iff_ne_zero.2 (by simpa using hB))
  rw [← PowerSeries.X_pow_dvd_iff, ← PowerSeries.X_pow_dvd_iff]
  exact hunit.dvd_mul_left

/-- The version actually needed by repeated left-endpoint blocks: different
nonzero local unit factors may be used at the distinct nodes. -/
theorem eq_zero_of_unit_weighted_jets {ι : Type*} [Fintype ι] (a : ι → K)
    (ha : Function.Injective a) (r : ι → ℕ) (B : ι → PowerSeries K)
    (hB : ∀ i, PowerSeries.coeff 0 (B i) ≠ 0) (p : K[X])
    (hdegree : p.natDegree < ∑ i, r i)
    (hjets : ∀ i j, j < r i →
      PowerSeries.coeff j (B i * (p.taylor (a i) : PowerSeries K)) = 0) : p = 0 := by
  apply eq_zero_of_confluent_jets a ha r p hdegree
  intro i j hj
  have hh := (unit_mul_jets_iff (B i) (p.taylor (a i)) (r i) (hB i)).1 (hjets i) j hj
  simpa using hh

noncomputable def confluentMatrix {ι : Type*} (a : ι → K) (r : ι → ℕ)
    {N : ℕ} (e : (Σ i, Fin (r i)) ≃ Fin N) : Matrix (Fin N) (Fin N) K :=
  fun i j => ((X ^ (j : ℕ) : K[X]).taylor (a (e.symm i).1)).coeff (e.symm i).2

theorem confluentMatrix_mulVec [DecidableEq K] {ι : Type*} (a : ι → K) (r : ι → ℕ)
    {N : ℕ} (e : (Σ i, Fin (r i)) ≃ Fin N) (v : Fin N → K) (i : Σ j, Fin (r j)) :
    (confluentMatrix a r e *ᵥ v) (e i) =
      ((Polynomial.ofFn N v).taylor (a i.1)).coeff i.2 := by
  classical
  have hidx : ((e.symm (e i)).2 : ℕ) = (i.2 : ℕ) :=
    congrArg (fun q : Σ j, Fin (r j) => (q.2 : ℕ)) (e.symm_apply_apply i)
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [map_sum, Polynomial.finsetSum_coeff, Polynomial.taylor_monomial,
    Polynomial.coeff_C_mul, Matrix.mulVec, dotProduct, confluentMatrix,
    Equiv.symm_apply_apply, Polynomial.taylor_X_pow, mul_comm, hidx]

/-- The confluent Taylor matrix is nonsingular for arbitrary multiplicities.
No characteristic-zero assumption or factorial divisions are needed. -/
theorem confluentMatrix_det_ne_zero {ι : Type*} [Fintype ι] (a : ι → K)
    (ha : Function.Injective a) (r : ι → ℕ) {N : ℕ}
    (e : (Σ i, Fin (r i)) ≃ Fin N) : (confluentMatrix a r e).det ≠ 0 := by
  classical
  by_cases hN : N = 0
  · subst N
    simp
  have hNsum : N = ∑ i, r i := by
    simpa using (Fintype.card_congr e).symm
  intro hdet
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hp : Polynomial.ofFn N v = 0 := by
    apply eq_zero_of_confluent_jets a ha r
    · rw [← hNsum]
      exact Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.2 hN) v
    · intro i j hj
      have hh := congrFun hz (e ⟨i, ⟨j, hj⟩⟩)
      simpa only [confluentMatrix_mulVec, Pi.zero_apply] using hh
  apply hv
  apply Polynomial.injective_ofFn N
  simpa using hp

end OddPiPowers
