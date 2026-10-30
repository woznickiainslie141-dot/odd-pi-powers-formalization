module

public import OddPiPowers.Analysis.BalancedSeriesFactors

/-! Polynomial-loss heights for the actual balanced local coefficients. -/

@[expose] public section

namespace OddPiPowers

open scoped PowerSeries BigOperators

noncomputable def balancedLocalMajorant (M m n : ℕ) : ℚ :=
  (2 : ℚ) ^ (M * n) * ((M + 2 * m + 1 : ℕ) : ℚ) ^ m * ((n : ℚ) + 1) ^ (2 * m)

theorem balancedBinomialWeight_abs (n ell : ℕ) :
    |balancedBinomialWeight n ell| = (n.choose ell : ℚ) := by
  unfold balancedBinomialWeight
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]

theorem balancedBinomialWeight_abs_le (n ell : ℕ) :
    |balancedBinomialWeight n ell| ≤ (2 : ℚ) ^ n := by
  rw [balancedBinomialWeight_abs]
  exact_mod_cast Nat.choose_le_two_pow n ell

theorem balancedWeightedFactors_coeff_bound (M n ell h q m : ℕ)
    (hell : ell ≤ n) (hh : h ≤ m) (hq : q ≤ m) :
    |PowerSeries.coeff q (((balancedWeightedFactors M n ell h).map Prod.fst).prod)| ≤
      ((M + 2 * m + 1 : ℕ) : ℚ) ^ m * ((n : ℚ) + 1) ^ (2 * m) := by
  let T := (balancedWeightedFactors M n ell h).length
  have hlen := balancedWeightedFactors_length M n ell h
  have hcap : T + m + 1 ≤ (M + 2 * m + 1) * (n + 1) := by
    dsimp [T]
    nlinarith
  have hcapQ : ((T + m + 1 : ℕ) : ℚ) ≤
      ((M + 2 * m + 1 : ℕ) : ℚ) * ((n : ℚ) + 1) := by exact_mod_cast hcap
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (T + m + 1)) hcapQ m
  have hc := (choose_coefficient_majorant_le_pow T q m hq).trans hp
  have hnum : ((n : ℚ) + 1) ^ h ≤ ((n : ℚ) + 1) ^ m :=
    pow_le_pow_right₀ (by have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n; linarith) hh
  have hcoef := coeff_list_prod_abs_le (balancedWeightedFactors M n ell h)
    (fun p hp => (balancedWeightedFactors_bounds M n ell h hell p hp).1)
    (fun p hp q => (balancedWeightedFactors_bounds M n ell h hell p hp).2 q) q
  rw [balancedWeightedFactors_weight] at hcoef
  calc
    _ ≤ ((n : ℚ) + 1) ^ h * ((T + q).choose q : ℚ) := hcoef
    _ ≤ ((n : ℚ) + 1) ^ m *
        (((M + 2 * m + 1 : ℕ) : ℚ) * ((n : ℚ) + 1)) ^ m :=
      mul_le_mul hnum hc (by positivity) (by positivity)
    _ = _ := by rw [mul_pow, show 2 * m = m + m by omega, pow_add]; ring

theorem balanced_localExpansion_coeff_abs_le (M n ell h q m : ℕ)
    (hell : ell ≤ n) (hh : h ≤ m) (hq : q ≤ m) :
    |PowerSeries.coeff q ((balancedActualFamily M n).localExpansion ell h)| ≤
      balancedLocalMajorant M m n := by
  have hw : |balancedBinomialWeight n ell| ^ M ≤ (2 : ℚ) ^ (M * n) := by
    calc
      _ ≤ ((2 : ℚ) ^ n) ^ M :=
        pow_le_pow_left₀ (abs_nonneg _) (balancedBinomialWeight_abs_le n ell) M
      _ = _ := by rw [← pow_mul, Nat.mul_comm n M]
  rw [balanced_localExpansion M n ell h hell, PowerSeries.coeff_C_mul, abs_mul, abs_pow]
  rw [← balancedWeightedFactors_prod]
  have ht := mul_le_mul hw (balancedWeightedFactors_coeff_bound M n ell h q m hell hh hq)
    (abs_nonneg _) (by positivity)
  unfold balancedLocalMajorant
  exact ht.trans_eq (by ring)

theorem balanced_localCoefficient_abs_le (M n ell h j : ℕ)
    (hell : ell ≤ n) (hh : h ≤ M - 1) :
    |(balancedActualFamily M n).localCoefficient ell h j| ≤ balancedLocalMajorant M (M - 1) n := by
  rw [ActualIntervals.localCoefficient, balanced_multiplicity M n ell hell]
  split_ifs with hj
  · exact balanced_localExpansion_coeff_abs_le M n ell h (M - 1 - j) (M - 1)
      hell hh (Nat.sub_le _ _)
  · simp only [abs_zero]
    unfold balancedLocalMajorant
    positivity

end OddPiPowers
