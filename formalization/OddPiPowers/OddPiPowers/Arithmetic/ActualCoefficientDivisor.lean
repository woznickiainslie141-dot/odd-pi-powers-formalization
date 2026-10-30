module

public import OddPiPowers.Arithmetic.LocalPrimeValuation

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators PowerSeries

theorem auxiliaryScale_primeValuation_lower {p M n j : ℕ} [Fact p.Prime]
    (hp_le : p ≤ n) (hn : n < p * p) (hj : j ≤ M - 1) :
    PrimeValuationLowerBound p ((M - 1 : ℕ) : ℤ)
      (auxiliaryScale M n j) := by
  let m := M - 1
  have hdvd : j.factorial ∣ m.factorial := Nat.factorial_dvd_factorial hj
  let q := m.factorial / j.factorial
  have hfac : j.factorial * q = m.factorial := Nat.mul_div_cancel' hdvd
  have hq0 : q ≠ 0 := by
    intro hq
    have hm0 : m.factorial = 0 := by simpa [hq] using hfac.symm
    exact (Nat.factorial_ne_zero m) hm0
  have hfacQ : (m.factorial : ℚ) = (j.factorial : ℚ) * (q : ℚ) := by
    exact_mod_cast hfac.symm
  have hscale : auxiliaryScale M n j =
      (q : ℚ) * (intervalLcm n : ℚ) ^ m := by
    unfold auxiliaryScale
    dsimp [m]
    rw [hfacQ]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)]
  have hqval : 0 ≤ padicValRat p (q : ℚ) := by
    exact_mod_cast (Nat.zero_le (padicValNat p q))
  have hlcmnz : (intervalLcm n : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (intervalLcm_pos n))
  have hlcmval : padicValRat p (intervalLcm n : ℚ) = 1 :=
    padicValRat_intervalLcm_eq_one hp_le hn
  apply Or.inr
  rw [hscale, padicValRat.mul (by exact_mod_cast hq0) (pow_ne_zero _ hlcmnz),
    padicValRat.pow, hlcmval]
  have hnonneg : 0 ≤ (m : ℤ) := by positivity
  omega

theorem primeValuationLowerBound_coeff_pow {p : ℕ} [Fact p.Prime]
    {f : PowerSeries ℚ} (hf : ∀ k : ℕ,
      PrimeValuationLowerBound p (-(k : ℤ)) (PowerSeries.coeff k f)) :
    ∀ (m k : ℕ),
      PrimeValuationLowerBound p (-(k : ℤ)) (PowerSeries.coeff k (f ^ m)) := by
  intro m
  induction m with
  | zero =>
      intro k
      by_cases hk : k = 0
      · subst k
        simp [PrimeValuationLowerBound]
      · left
        simp [hk]
  | succ m ih =>
      intro k
      have hmul := primeValuationLowerBound_coeff_mul
        (a := 0) (b := 0)
        (fun i => by simpa using ih i)
        (fun i => by simpa using hf i) k
      simpa [pow_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmul

private theorem actualAuxiliary_coeff_at_ell {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) (ell : ℕ) (hell : ell ≤ P.n) :
    (actualAuxiliary P h j).coeff (P.n - ell) =
      auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val := by
  classical
  rw [actualAuxiliary, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem ell
    (Finset.mem_range.mpr (by omega : ell < P.n + 1))]
  · rw [Polynomial.coeff_C_mul_X_pow]
    simp
  · intro r hr hne
    have hrn : r ≤ P.n := by
      have hr' := Finset.mem_range.mp hr
      omega
    have hpow : P.n - r ≠ P.n - ell := by
      intro heq
      have hrEq : r = ell := by omega
      exact hne hrEq
    rw [Polynomial.coeff_C_mul_X_pow]
    simp [Ne.symm hpow]

theorem actualAuxiliaryInt_coeff_cast_at_ell {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) (ell : ℕ) (hell : ell ≤ P.n) :
    ((actualAuxiliaryInt P h j).coeff (P.n - ell) : ℚ) =
      auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val := by
  have hmap := congrArg (fun f : Polynomial ℚ => f.coeff (P.n - ell))
    (map_actualAuxiliaryInt P h j)
  rw [Polynomial.coeff_map] at hmap
  rw [actualAuxiliary_coeff_at_ell P h j ell hell] at hmap
  exact hmap

private theorem intCoeff_dvd_of_primeValuationLowerBound {p n : ℕ}
    [Fact p.Prime] {z : ℤ}
    (h : PrimeValuationLowerBound p (n : ℤ) (z : ℚ)) :
    (p : ℤ) ^ n ∣ z := by
  rcases h with hz | hval
  · have hzInt : z = 0 := by exact_mod_cast hz
    simp [hzInt]
  · rw [padicValRat.of_int] at hval
    exact (padicValInt_dvd_iff n z).2 (Or.inr (by exact_mod_cast hval))

theorem actualAuxiliaryInt_coeff_cast {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) (k : ℕ) :
    ((actualAuxiliaryInt P h j).coeff k : ℚ) =
      (actualAuxiliary P h j).coeff k := by
  have hmap := congrArg (fun f : Polynomial ℚ => f.coeff k)
    (map_actualAuxiliaryInt P h j)
  rw [Polynomial.coeff_map] at hmap
  exact hmap

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

private theorem localFactor_coeff_lower {p ell u : ℕ} [Fact p.Prime]
    (a : Fin M) (hell : ell ≤ P.n) (hn : P.n < p * p) :
    PrimeValuationLowerBound p
      (((P.intervalCarryNat a p ell : ℕ) : ℤ) -
        (if ell ∈ P.interval a then 0 else 1) - (u : ℤ))
      (PowerSeries.coeff u (P.localFactor a ell)) := by
  by_cases hmem : ell ∈ P.interval a
  · simpa [localFactor, hmem, sub_eq_add_neg, add_assoc] using
      P.poleLocalFactor_coeff_lower a hmem hn (u := u)
  · simpa [localFactor, hmem, sub_eq_add_neg, add_assoc] using
      P.regularLocalFactor_coeff_lower a hell hmem hn (u := u)

private theorem sumLocalBudgets_eq (ell p : ℕ) :
    (∑ a : Fin M,
      (((P.intervalCarryNat a p ell : ℕ) : ℤ) -
        (if ell ∈ P.interval a then 0 else 1))) =
      (P.carryWeight p ell : ℤ) - (M - P.multiplicity ell : ℤ) := by
  classical
  have hcountNat :
      (Finset.univ.filter fun a : Fin M => ell ∉ P.interval a).card =
        M - P.multiplicity ell := by
    have hrewrite :
        (Finset.univ.filter fun a : Fin M => ell ∈ P.interval a).card =
          P.multiplicity ell := by
      rfl
    have hcard := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun a : Fin M => ell ∈ P.interval a)
    rw [hrewrite, Finset.card_univ, Fintype.card_fin] at hcard
    have hreg :
        (Finset.univ.filter fun a : Fin M => ¬ ell ∈ P.interval a).card +
          P.multiplicity ell = M := by
      simpa [add_comm] using hcard
    omega
  have hmu : P.multiplicity ell ≤ M := by
    unfold ActualIntervals.multiplicity
    simpa using Finset.card_le_card (show
      (Finset.univ.filter fun a : Fin M => ell ∈ P.interval a) ⊆ Finset.univ from
      fun _ _ => Finset.mem_univ _)
  have hcount :
      (∑ a : Fin M,
        (if ell ∈ P.interval a then (0 : ℤ) else 1)) =
        ((M - P.multiplicity ell : ℕ) : ℤ) := by
    calc
      _ = ∑ a ∈ Finset.univ,
            (if ell ∉ P.interval a then (1 : ℤ) else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              by_cases hm : ell ∈ P.interval a <;> simp [hm]
      _ = ((Finset.univ.filter fun a : Fin M => ell ∉ P.interval a).card : ℤ) := by
            rw [← Finset.sum_boole]
      _ = ((M - P.multiplicity ell : ℕ) : ℤ) := by rw [hcountNat]
  calc
    _ = (∑ a : Fin M, (P.intervalCarryNat a p ell : ℤ)) -
          ∑ a : Fin M, (if ell ∈ P.interval a then (0 : ℤ) else 1) := by
            rw [Finset.sum_sub_distrib]
    _ = (P.carryWeight p ell : ℤ) - (M - P.multiplicity ell : ℤ) := by
          rw [hcount]
          rw [Nat.cast_sub hmu]
          simp [carryWeight, Nat.cast_sum]

theorem localExpansion_coeff_lower {p ell h q : ℕ} [Fact p.Prime]
    (hell : ell ≤ P.n) (hp_le : p ≤ P.n) (hn : P.n < p * p) :
    PrimeValuationLowerBound p
      ((P.carryWeight p ell : ℤ) - (M - P.multiplicity ell : ℤ) - q)
      (PowerSeries.coeff q (P.localExpansion ell h)) := by
  have hlin := primeValuationLowerBound_intLinear (p := p) ell
  have hpow := primeValuationLowerBound_coeff_pow hlin h
  let b : Fin M → ℤ := fun a =>
    (((P.intervalCarryNat a p ell : ℕ) : ℤ) -
      (if ell ∈ P.interval a then 0 else 1))
  have hprod : ∀ k : ℕ,
      PrimeValuationLowerBound p ((∑ a : Fin M, b a) - (k : ℤ))
        (PowerSeries.coeff k (∏ a : Fin M, P.localFactor a ell)) := by
    intro k
    exact primeValuationLowerBound_finset_prod_coeff
      (Finset.univ : Finset (Fin M)) (fun a => P.localFactor a ell) b
      (by
        intro a ha i
        exact localFactor_coeff_lower P a hell hn (u := i)) k
  have hbudget :
      (∑ a : Fin M,
        b a) =
        (P.carryWeight p ell : ℤ) - (M - P.multiplicity ell : ℤ) :=
    by simpa [b] using sumLocalBudgets_eq P ell p
  have hmul := primeValuationLowerBound_coeff_mul
    (a := 0) (b := ∑ a : Fin M, b a)
    (fun k => by simpa using hpow k) hprod q
  rw [localExpansion]
  rw [hbudget] at hmul
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmul

theorem actualAuxiliaryInt_coeff_primePower_dvd {p : ℕ} [Fact p.Prime]
    (P : ActualIntervals M) (h j : Fin M) (ell : ℕ)
    (hp_le : p ≤ P.n) (hn : P.n < p * p) (hell : ell ≤ P.n) :
    (p : ℤ) ^ (P.carryWeight p ell + j.val) ∣
      (actualAuxiliaryInt P h j).coeff (P.n - ell) := by
  let μ := P.multiplicity ell
  let W := P.carryWeight p ell
  have hjM : j.val ≤ M - 1 := by omega
  have hscale := auxiliaryScale_primeValuation_lower hp_le hn hjM
  have hcoeffCast := actualAuxiliaryInt_coeff_cast_at_ell P h j ell hell
  by_cases hjlt : j.val < μ
  · let u := μ - 1 - j.val
    have hlocal := P.localExpansion_coeff_lower hell hp_le hn
      (h := h.val) (q := u)
    have hmuM : μ ≤ M := by
      dsimp [μ]
      unfold ActualIntervals.multiplicity
      simpa using Finset.card_le_card (show
        (Finset.univ.filter fun a : Fin M => ell ∈ P.interval a) ⊆ Finset.univ from
        fun _ _ => Finset.mem_univ _)
    have hbudget :
        ((M - 1 : ℕ) : ℤ) + (W : ℤ) - (M - μ : ℤ) - (u : ℤ) =
          (W + j.val : ℤ) := by
      dsimp [u]
      omega
    have hmul := primeValuationLowerBound_mul hscale hlocal
    have hvalue :
        PrimeValuationLowerBound p (W + j.val : ℤ)
          (auxiliaryScale M P.n j.val *
            PowerSeries.coeff u (P.localExpansion ell h.val)) := by
      apply primeValuationLowerBound_mono hmul
      omega
    have hlocalCoeff : P.localCoefficient ell h.val j.val =
        PowerSeries.coeff u (P.localExpansion ell h.val) := by
      simp [ActualIntervals.localCoefficient, hjlt, μ, u]
    have hvalue' :
        PrimeValuationLowerBound p (W + j.val : ℤ)
          (((actualAuxiliaryInt P h j).coeff (P.n - ell) : ℤ) : ℚ) := by
      rw [hcoeffCast, hlocalCoeff]
      exact hvalue
    have hdvd := intCoeff_dvd_of_primeValuationLowerBound hvalue'
    simpa [W] using hdvd
  · have hlocalZero : P.localCoefficient ell h.val j.val = 0 := by
      simp [ActualIntervals.localCoefficient, hjlt, μ]
    have hcoefZero :
        ((actualAuxiliaryInt P h j).coeff (P.n - ell) : ℚ) = 0 := by
      rw [hcoeffCast, hlocalZero]
      simp
    have hz : (actualAuxiliaryInt P h j).coeff (P.n - ell) = 0 := by
      exact_mod_cast hcoefZero
    simp [hz]

theorem actualAuxiliaryInt_coeff_primePower_dvd_all {p k : ℕ} [Fact p.Prime]
    (h j : Fin M) (hp_le : p ≤ P.n) (hn : P.n < p * p) :
    (p : ℤ) ^ (P.carryWeight p (P.n - k) + j.val) ∣
      (actualAuxiliaryInt P h j).coeff k := by
  by_cases hk : k ≤ P.n
  · let ell := P.n - k
    have hell : ell ≤ P.n := by dsimp [ell]; omega
    have hdvd := P.actualAuxiliaryInt_coeff_primePower_dvd h j ell hp_le hn hell
    have hindex : P.n - ell = k := by dsimp [ell]; omega
    rw [hindex] at hdvd
    simpa [ell] using hdvd
  · have hdeg : (actualAuxiliary P h j).natDegree < k := by
      have h := actualAuxiliary_natDegree_le P h j
      omega
    have hzeroQ : (actualAuxiliary P h j).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
    have hcast := actualAuxiliaryInt_coeff_cast P h j k
    have hzero : (actualAuxiliaryInt P h j).coeff k = 0 := by
      exact_mod_cast (hcast.trans hzeroQ)
    simp [hzero]

/-- The minimum of all carry weights at integer nodes from zero through `n`. -/
noncomputable def carryWeightMinimum (p : ℕ) : ℕ :=
  (Finset.range (P.n + 1)).inf'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ P.n)⟩
    (fun ell => P.carryWeight p ell)

theorem carryWeightMinimum_le (p ell : ℕ) (hell : ell ≤ P.n) :
    P.carryWeightMinimum p ≤ P.carryWeight p ell :=
  Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

/-- Finite set of primes used in the common arithmetic divisor. -/
def admissiblePrimeIndices (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter
    (fun p => Nat.Prime p ∧ p ≤ n ∧ n < p * p)

/-- The explicit common prime-power divisor of the actual auxiliary polynomials. -/
noncomputable def actualAuxiliaryPrimeDivisor : ℕ :=
  ∏ p ∈ admissiblePrimeIndices P.n, p ^ P.carryWeightMinimum p

theorem actualAuxiliaryPrimeDivisor_pos : 0 < P.actualAuxiliaryPrimeDivisor := by
  classical
  unfold actualAuxiliaryPrimeDivisor
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2.1) _

theorem actualAuxiliaryPrimeDivisor_dvd_coeff {h j : Fin M} (k : ℕ) :
    P.actualAuxiliaryPrimeDivisor ∣
      ((actualAuxiliaryInt P h j).coeff k).natAbs := by
  classical
  let s := admissiblePrimeIndices P.n
  change (∏ p ∈ s, p ^ P.carryWeightMinimum p) ∣
    ((actualAuxiliaryInt P h j).coeff k).natAbs
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
    have hqp : Nat.Prime q := (Finset.mem_filter.mp hq).2.1
    have hneq : p ≠ q := fun heq => hpq heq
    exact Nat.coprime_iff_isRelPrime.mp
      (Nat.coprime_pow_primes _ _ hpp hqp hneq)
  · intro p hp
    have hpdata := (Finset.mem_filter.mp hp).2
    letI : Fact p.Prime := ⟨hpdata.1⟩
    have hpCoeff := actualAuxiliaryInt_coeff_primePower_dvd_all
      (P := P) (p := p) (k := k) h j
      hpdata.2.1 hpdata.2.2
    have hpCoeffNat : p ^ (P.carryWeight p (P.n - k) + j.val) ∣
        ((actualAuxiliaryInt P h j).coeff k).natAbs :=
      Int.natCast_dvd.mp (by simpa using hpCoeff)
    have hmin := P.carryWeightMinimum_le p (P.n - k) (Nat.sub_le _ _)
    exact dvd_trans (pow_dvd_pow p (by omega)) hpCoeffNat

theorem actualAuxiliaryPrimeDivisor_dvd_intCoeff {h j : Fin M} (k : ℕ) :
    (P.actualAuxiliaryPrimeDivisor : ℤ) ∣
      (actualAuxiliaryInt P h j).coeff k := by
  apply Int.natCast_dvd.mpr
  exact P.actualAuxiliaryPrimeDivisor_dvd_coeff (h := h) (j := j) k

end ActualIntervals

end OddPiPowers

end
