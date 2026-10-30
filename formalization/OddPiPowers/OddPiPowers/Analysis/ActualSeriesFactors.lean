module

public import OddPiPowers.Analysis.BalancedSeriesFactors
public import Mathlib.Data.Nat.Choose.Bounds

/-! Draft weighted lists for the general actual interval factors.
This file has not been compiled by the helper. -/

@[expose] public section

namespace OddPiPowers

open scoped PowerSeries BigOperators

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def actualFactorWeight (a : Fin M) : ℚ :=
  ((P.n : ℚ) + 1) * 2 ^ P.length a

theorem binomialWeight_abs_le (a : Fin M) (r : ℕ) :
    |P.binomialWeight a r| ≤ (2 : ℚ) ^ P.length a := by
  have hc := Nat.choose_le_two_pow (P.length a) (r - P.left a)
  have hcQ : (Nat.choose (P.length a) (r - P.left a) : ℚ) ≤
      (2 : ℚ) ^ P.length a := by exact_mod_cast hc
  simpa [ActualIntervals.binomialWeight, abs_mul, abs_pow] using hcQ

theorem regularReciprocal_coeff_abs_le_one (e : ℤ) (he : e ≠ 0) (q : ℕ) :
    |PowerSeries.coeff q (regularReciprocal e)| ≤ (1 : ℚ) := by
  have he1 : (1 : ℚ) ≤ |(e : ℚ)| := by
    rcases lt_or_gt_of_ne he with hn | hp
    · have hq : (e : ℚ) ≤ -1 := by exact_mod_cast (show e ≤ -1 by omega)
      rw [abs_of_nonpos (by linarith : (e : ℚ) ≤ 0)]
      linarith
    · have hq : (1 : ℚ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
      rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ e)]
      exact hq
  have hinv : |1 / (e : ℚ)| ≤ 1 := by
    rw [abs_div, abs_one]
    exact (div_le_one (by linarith)).2 he1
  have hn := normalizedReciprocal_coeff_abs_le_one e he q
  rw [regularReciprocal, PowerSeries.coeff_C_mul, abs_mul]
  simpa using mul_le_mul hinv hn (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)

theorem regularLocalFactor_coeff_abs_le (a : Fin M) (ell q : ℕ)
    (hregular : ell ∉ P.interval a) :
    |PowerSeries.coeff q (P.regularLocalFactor a ell)| ≤ actualFactorWeight P a := by
  have hcard : (P.interval a).card ≤ P.n + 1 := by
    rw [P.interval_card_eq_length_add_one]
    unfold ActualIntervals.length
    omega
  unfold ActualIntervals.regularLocalFactor
  rw [map_sum]
  calc
    _ ≤ ∑ r ∈ P.interval a,
        |PowerSeries.coeff q (PowerSeries.C (P.binomialWeight a r) *
          regularReciprocal ((r : ℤ) - (ell : ℤ)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ P.interval a, (2 : ℚ) ^ P.length a := by
      apply Finset.sum_le_sum
      intro r hr
      have hne : (r : ℤ) - (ell : ℤ) ≠ 0 := by
        intro he
        have hre : r = ell := by exact_mod_cast (sub_eq_zero.mp he)
        apply hregular
        simpa [hre] using hr
      rw [PowerSeries.coeff_C_mul, abs_mul]
      have hw := binomialWeight_abs_le P a r
      have hr' := regularReciprocal_coeff_abs_le_one _ hne q
      have hm := mul_le_mul hw hr' (abs_nonneg _) (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ P.length a)
      simpa using hm
    _ = ((P.interval a).card : ℚ) * (2 : ℚ) ^ P.length a := by simp
    _ ≤ actualFactorWeight P a := by
      unfold actualFactorWeight
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

noncomputable def actualLocalWeightedFactors (a : Fin M) (ell : ℕ) :
    List (PowerSeries ℚ × ℚ) :=
  if ell ∈ P.interval a then
    [(PowerSeries.C (P.binomialWeight a ell), actualFactorWeight P a)] ++
      ((P.interval a).erase ell).toList.map
        (fun r : ℕ => (normalizedReciprocal ((r : ℤ) - (ell : ℤ)), 1))
  else [(P.regularLocalFactor a ell, actualFactorWeight P a)]

theorem actualLocalWeightedFactors_prod (a : Fin M) (ell : ℕ) :
    ((actualLocalWeightedFactors P a ell).map Prod.fst).prod = P.localFactor a ell := by
  classical
  by_cases he : ell ∈ P.interval a
  · simp [actualLocalWeightedFactors, ActualIntervals.localFactor, he,
      ActualIntervals.poleLocalFactor, List.map_map]
  · simp [actualLocalWeightedFactors, ActualIntervals.localFactor, he]

theorem actualLocalWeightedFactors_weight (a : Fin M) (ell : ℕ) :
    ((actualLocalWeightedFactors P a ell).map Prod.snd).prod = actualFactorWeight P a := by
  classical
  by_cases he : ell ∈ P.interval a <;>
    simp [actualLocalWeightedFactors, he, List.map_map]

theorem actualLocalWeightedFactors_length (a : Fin M) (ell : ℕ) :
    (actualLocalWeightedFactors P a ell).length ≤ P.n + 2 := by
  classical
  by_cases he : ell ∈ P.interval a
  · have hc := Finset.card_le_card (Finset.erase_subset ell (P.interval a))
    have hlen : P.length a ≤ P.n := by unfold ActualIntervals.length; omega
    simp only [actualLocalWeightedFactors, he, ite_true, List.length_append,
      List.length_cons, List.length_nil, List.length_map, Finset.length_toList]
    rw [P.interval_card_eq_length_add_one] at hc
    omega
  · simp [actualLocalWeightedFactors, he]

theorem actualLocalWeightedFactors_bounds (a : Fin M) (ell : ℕ) :
    ∀ p ∈ actualLocalWeightedFactors P a ell,
      0 ≤ p.2 ∧ ∀ q, |PowerSeries.coeff q p.1| ≤ p.2 := by
  classical
  intro p hp
  by_cases he : ell ∈ P.interval a
  · simp only [actualLocalWeightedFactors, he, ite_true, List.mem_append,
      List.mem_singleton] at hp
    rcases hp with hp | hp
    · subst p
      constructor
      · unfold actualFactorWeight; positivity
      · intro q
        have hw := binomialWeight_abs_le P a ell
        have hbig : (2 : ℚ) ^ P.length a ≤ actualFactorWeight P a := by
          unfold actualFactorWeight
          have hn : (1 : ℚ) ≤ (P.n : ℚ) + 1 := by
            have hn0 : (0 : ℚ) ≤ P.n := Nat.cast_nonneg _
            linarith
          nlinarith [pow_nonneg (show (0 : ℚ) ≤ 2 by norm_num) (P.length a)]
        rw [PowerSeries.coeff_C]
        split_ifs with hq
        · exact hw.trans hbig
        · simp only [abs_zero]
          unfold actualFactorWeight
          positivity
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      have hr' : r ∈ (P.interval a).erase ell := by simpa using hr
      have hne : (r : ℤ) - (ell : ℤ) ≠ 0 := by
        have hrl := (Finset.mem_erase.mp hr').1
        omega
      exact ⟨by norm_num, fun q => normalizedReciprocal_coeff_abs_le_one _ hne q⟩
  · simp only [actualLocalWeightedFactors, he, ite_false, List.mem_singleton] at hp
    subst p
    exact ⟨by unfold actualFactorWeight; positivity,
      fun q => regularLocalFactor_coeff_abs_le P a ell q he⟩

noncomputable def actualWeightedFactors (ell h : ℕ) : List (PowerSeries ℚ × ℚ) :=
  List.replicate h (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X, (P.n : ℚ) + 1) ++
    ((Finset.univ : Finset (Fin M)).toList.map
      (fun a : Fin M => actualLocalWeightedFactors P a ell)).flatten

theorem actualWeightedFactors_prod (ell h : ℕ) :
    ((actualWeightedFactors P ell h).map Prod.fst).prod = P.localExpansion ell h := by
  classical
  simp [actualWeightedFactors, ActualIntervals.localExpansion, List.map_flatten,
    List.prod_flatten, List.map_map, actualLocalWeightedFactors_prod]

theorem actualWeightedFactors_weight (ell h : ℕ) :
    ((actualWeightedFactors P ell h).map Prod.snd).prod =
      ((P.n : ℚ) + 1) ^ (h + M) *
        (2 : ℚ) ^ (∑ a : Fin M, P.length a) := by
  classical
  simp [actualWeightedFactors, List.map_flatten, List.prod_flatten, List.map_map,
    Function.comp_def, actualLocalWeightedFactors_weight, actualFactorWeight, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, pow_add]
  ring

theorem actualWeightedFactors_length (ell h : ℕ) :
    (actualWeightedFactors P ell h).length ≤ h + M * (P.n + 2) := by
  classical
  simp only [actualWeightedFactors, List.length_append, List.length_replicate,
    List.length_flatten, List.map_map, Function.comp_def]
  have hsum : (((Finset.univ : Finset (Fin M)).toList.map
      (fun a => (actualLocalWeightedFactors P a ell).length)).sum) ≤ M * (P.n + 2) := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M)))
      (fun a _ => actualLocalWeightedFactors_length P a ell)
  omega

theorem actualWeightedFactors_bounds (ell h : ℕ) (hell : ell ≤ P.n) :
    ∀ p ∈ actualWeightedFactors P ell h,
      0 ≤ p.2 ∧ ∀ q, |PowerSeries.coeff q p.1| ≤ p.2 := by
  classical
  intro p hp
  rw [actualWeightedFactors, List.mem_append] at hp
  rcases hp with hp | hp
  · have he := List.eq_of_mem_replicate hp
    subst p
    exact ⟨by positivity, fun q => numeratorSeries_coeff_abs_le P.n ell q hell⟩
  · obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
    exact actualLocalWeightedFactors_bounds P a ell p hp

end OddPiPowers
