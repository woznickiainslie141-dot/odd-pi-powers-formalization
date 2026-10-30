module

public import OddPiPowers.Analysis.ActualSeriesFactors

/-! General actual local heights with a harmless fixed polynomial loss. -/

@[expose] public section

namespace OddPiPowers

open scoped PowerSeries BigOperators

variable {M : ℕ} (P : ActualIntervals M)

theorem actual_multiplicity_le (ell : ℕ) : P.multiplicity ell ≤ M := by
  have ht := Finset.card_le_card (Finset.filter_subset
    (fun a : Fin M => ell ∈ P.interval a) Finset.univ)
  simpa only [ActualIntervals.multiplicity, Finset.card_univ, Fintype.card_fin] using ht

noncomputable def actualLocalMajorant (m : ℕ) : ℚ :=
  (2 : ℚ) ^ (∑ a : Fin M, P.length a) *
    ((2 * M + 2 * m + 1 : ℕ) : ℚ) ^ m * ((P.n : ℚ) + 1) ^ (2 * m + M)

theorem actualLocalMajorant_pos (m : ℕ) : 0 < actualLocalMajorant P m := by
  unfold actualLocalMajorant
  positivity

theorem actual_localExpansion_coeff_abs_le (ell h q m : ℕ)
    (hell : ell ≤ P.n) (hh : h ≤ m) (hq : q ≤ m) :
    |PowerSeries.coeff q (P.localExpansion ell h)| ≤ actualLocalMajorant P m := by
  let T := (actualWeightedFactors P ell h).length
  have hlen := actualWeightedFactors_length P ell h
  have hcap : T + m + 1 ≤ (2 * M + 2 * m + 1) * (P.n + 1) := by
    dsimp [T]
    nlinarith
  have hcapQ : ((T + m + 1 : ℕ) : ℚ) ≤
      ((2 * M + 2 * m + 1 : ℕ) : ℚ) * ((P.n : ℚ) + 1) := by exact_mod_cast hcap
  have hc := (choose_coefficient_majorant_le_pow T q m hq).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg (T + m + 1)) hcapQ m)
  have hn1 : (1 : ℚ) ≤ (P.n : ℚ) + 1 := by
    have hn0 : (0 : ℚ) ≤ P.n := Nat.cast_nonneg _
    linarith
  have hp : ((P.n : ℚ) + 1) ^ (h + M) ≤ ((P.n : ℚ) + 1) ^ (m + M) :=
    pow_le_pow_right₀ hn1 (Nat.add_le_add_right hh M)
  have hcoef := coeff_list_prod_abs_le (actualWeightedFactors P ell h)
    (fun p hp => (actualWeightedFactors_bounds P ell h hell p hp).1)
    (fun p hp q => (actualWeightedFactors_bounds P ell h hell p hp).2 q) q
  rw [actualWeightedFactors_prod, actualWeightedFactors_weight] at hcoef
  calc
    _ ≤ (((P.n : ℚ) + 1) ^ (h + M) * (2 : ℚ) ^ (∑ a : Fin M, P.length a)) *
        ((T + q).choose q : ℚ) := hcoef
    _ ≤ (((P.n : ℚ) + 1) ^ (m + M) * (2 : ℚ) ^ (∑ a : Fin M, P.length a)) *
        (((2 * M + 2 * m + 1 : ℕ) : ℚ) * ((P.n : ℚ) + 1)) ^ m := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hp (by positivity)) hc (by positivity) (by positivity)
    _ = _ := by
      unfold actualLocalMajorant
      rw [mul_pow, show 2 * m + M = (m + M) + m by omega, pow_add]
      ring

theorem actual_localCoefficient_abs_le (ell h j : ℕ)
    (hell : ell ≤ P.n) (hh : h ≤ M - 1) :
    |P.localCoefficient ell h j| ≤ actualLocalMajorant P (M - 1) := by
  rw [ActualIntervals.localCoefficient]
  split_ifs with hj
  · exact actual_localExpansion_coeff_abs_le P ell h (P.multiplicity ell - 1 - j)
      (M - 1) hell hh (by have ht := actual_multiplicity_le P ell; omega)
  · simpa only [abs_zero] using (actualLocalMajorant_pos P (M - 1)).le

end OddPiPowers
