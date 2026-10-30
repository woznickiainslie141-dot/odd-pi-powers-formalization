module

public import OddPiPowers.Analysis.SeriesCoefficientMajorant
public import OddPiPowers.Construction.BalancedActualFamily
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! An explicit list retains all repeated reciprocal and numerator factors. -/

@[expose] public section

namespace OddPiPowers

open scoped PowerSeries BigOperators

theorem normalizedReciprocal_coeff_abs_le_one (e : ℤ) (he : e ≠ 0) (q : ℕ) :
    |PowerSeries.coeff q (normalizedReciprocal e)| ≤ (1 : ℚ) := by
  have he1 : (1 : ℚ) ≤ |(e : ℚ)| := by
    rcases lt_or_gt_of_ne he with hn | hp
    · have hq : (e : ℚ) ≤ -1 := by exact_mod_cast (show e ≤ -1 by omega)
      rw [abs_of_nonpos (by linarith : (e : ℚ) ≤ 0)]
      linarith
    · have hq : (1 : ℚ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
      rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ e)]
      exact hq
  simp only [normalizedReciprocal, PowerSeries.coeff_mk, abs_pow, abs_div, abs_neg, abs_one]
  exact pow_le_one₀ (by positivity) ((div_le_one (by linarith)).mpr he1)

theorem numeratorSeries_coeff_abs_le (n ell q : ℕ) (hell : ell ≤ n) :
    |PowerSeries.coeff q (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X)| ≤ (n : ℚ) + 1 := by
  rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
  by_cases hq0 : q = 0
  · subst q
    simp only [ite_true, Nat.zero_ne_one, ite_false, add_zero, abs_neg]
    rw [abs_of_nonneg (Nat.cast_nonneg ell)]
    exact_mod_cast (show ell ≤ n + 1 by omega)
  · by_cases hq1 : q = 1
    · simp only [ite_eq_right hq0, ite_eq_left hq1, zero_add, abs_one]
      have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      linarith
    · simp only [ite_eq_right hq0, ite_eq_right hq1, zero_add, abs_zero]
      positivity

noncomputable def reciprocalWeightedFactors (n ell : ℕ) : List (PowerSeries ℚ × ℚ) :=
  ((Finset.range (n + 1)).erase ell).toList.map
    (fun r : ℕ => (normalizedReciprocal ((r : ℤ) - (ell : ℤ)), 1))

noncomputable def balancedWeightedFactors (M n ell h : ℕ) : List (PowerSeries ℚ × ℚ) :=
  List.replicate h (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X, (n : ℚ) + 1) ++
    (List.replicate M (reciprocalWeightedFactors n ell)).flatten

theorem reciprocalWeightedFactors_prod (n ell : ℕ) :
    ((reciprocalWeightedFactors n ell).map Prod.fst).prod =
      ∏ r ∈ (Finset.range (n + 1)).erase ell,
        normalizedReciprocal ((r : ℤ) - (ell : ℤ)) := by
  simp [reciprocalWeightedFactors, List.map_map]

theorem balancedWeightedFactors_prod (M n ell h : ℕ) :
    ((balancedWeightedFactors M n ell h).map Prod.fst).prod =
      (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X) ^ h *
        (∏ r ∈ (Finset.range (n + 1)).erase ell,
          normalizedReciprocal ((r : ℤ) - (ell : ℤ))) ^ M := by
  simp [balancedWeightedFactors, List.map_flatten, List.prod_flatten,
    reciprocalWeightedFactors_prod]

theorem balancedWeightedFactors_weight (M n ell h : ℕ) :
    ((balancedWeightedFactors M n ell h).map Prod.snd).prod = ((n : ℚ) + 1) ^ h := by
  simp [balancedWeightedFactors, reciprocalWeightedFactors, List.map_flatten,
    List.prod_flatten, List.map_map]

theorem balancedWeightedFactors_length (M n ell h : ℕ) :
    (balancedWeightedFactors M n ell h).length ≤ h + M * (n + 1) := by
  simp only [balancedWeightedFactors, List.length_append, List.length_replicate,
    List.length_flatten, List.map_replicate, List.sum_replicate, nsmul_eq_mul,
    reciprocalWeightedFactors, List.length_map, Finset.length_toList]
  have hc := Finset.card_le_card (Finset.erase_subset ell (Finset.range (n + 1)))
  have he : ((Finset.range (n + 1)).erase ell).card ≤ n + 1 := by simpa using hc
  exact Nat.add_le_add_left (Nat.mul_le_mul_left M he) h

theorem balancedWeightedFactors_bounds (M n ell h : ℕ) (hell : ell ≤ n) :
    ∀ p ∈ balancedWeightedFactors M n ell h,
      0 ≤ p.2 ∧ ∀ q, |PowerSeries.coeff q p.1| ≤ p.2 := by
  intro p hp
  rw [balancedWeightedFactors, List.mem_append] at hp
  rcases hp with hp | hp
  · have he := List.eq_of_mem_replicate hp
    subst p
    exact ⟨by positivity, fun q => numeratorSeries_coeff_abs_le n ell q hell⟩
  · obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
    have he := List.eq_of_mem_replicate hl
    subst l
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    have hr' : r ∈ (Finset.range (n + 1)).erase ell := by simpa using hr
    have hne : (r : ℤ) - (ell : ℤ) ≠ 0 := by
      have hrl := (Finset.mem_erase.mp hr').1
      omega
    exact ⟨by norm_num, fun q => normalizedReciprocal_coeff_abs_le_one _ hne q⟩

end OddPiPowers
