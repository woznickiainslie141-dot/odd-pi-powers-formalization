/-
Copyright (c) 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Pinned Mathlib Stirling Part 1 only. The Wallis/normalization part is not needed.
See logs/p5e-stirling-core-provenance.json. -/

@[expose] public section

open scoped Topology Real Nat Asymptotics

open Nat hiding log log_pow
open Finset Filter Real

namespace OddPiPowers.StirlingLogCore

/-!
### Part 1
https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/


/-- Define `stirlingSeq n` as $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$.
Stirling's formula states that this sequence has limit $\sqrt(π)$.
-/
noncomputable def stirlingSeq (n : ℕ) : ℝ :=
  n ! / (√(2 * n : ℝ) * (n / exp 1) ^ n)

@[simp]
theorem stirlingSeq_zero : stirlingSeq 0 = 0 := by
  rw [stirlingSeq, cast_zero, mul_zero, Real.sqrt_zero, zero_mul, div_zero]

@[simp]
theorem stirlingSeq_one : stirlingSeq 1 = exp 1 / √2 := by
  rw [stirlingSeq, pow_one, factorial_one, cast_one, mul_one, mul_one_div, one_div_div]

theorem log_stirlingSeq_formula (n : ℕ) :
    log (stirlingSeq n) = Real.log n ! - 1 / 2 * Real.log (2 * n) - n * log (n / exp 1) := by
  cases n
  · simp
  · rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub]
      <;> positivity

/-- The sequence `log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))` has the series expansion
`∑ 1 / (2 * (k + 1) + 1) * (1 / 2 * (m + 1) + 1)^(2 * (k + 1))`. -/
theorem log_stirlingSeq_sdiff_hasSum (m : ℕ) :
    HasSum (fun k : ℕ => (1 : ℝ) / (2 * ↑(k + 1) + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ ↑(k + 1))
      (log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))) := by
  let f (k : ℕ) := (1 : ℝ) / (2 * k + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ k
  change HasSum (fun k => f (k + 1)) _
  rw [hasSum_nat_add_iff]
  convert (hasSum_log_one_add_inv m.cast_add_one_pos).mul_left ((↑(m + 1) : ℝ) + 1 / 2) using 1
  · ext k
    dsimp only [f]
    rw [← pow_mul, pow_add]
    push_cast
    field
  · have h (x) (hx : x ≠ (0 : ℝ)) : 1 + x⁻¹ = (x + 1) / x := by field
    simp (disch := positivity) only [log_stirlingSeq_formula, log_div, log_mul, log_exp,
      factorial_succ, cast_mul, cast_succ, range_one, sum_singleton, h]
    ring


/-- The sequence `log ∘ stirlingSeq ∘ succ` is monotone decreasing -/
theorem log_stirlingSeq'_antitone : Antitone (Real.log ∘ stirlingSeq ∘ succ) :=
  antitone_nat_of_succ_le fun n =>
    sub_nonneg.mp <| (log_stirlingSeq_sdiff_hasSum n).nonneg fun m => by positivity

/-- **Robbins' sharp stepwise bound** for the Stirling sequence:
`log (stirlingSeq n) - log (stirlingSeq (n+1)) ≤ 1 / (12 n (n + 1))`. -/
theorem log_stirlingSeq_sdiff_le (n : ℕ) :
    log (stirlingSeq n) - log (stirlingSeq (n + 1)) ≤ 1 / (12 * n * (n + 1)) := by
  rcases n with (_ | n)
  · suffices 0 ≤ Real.log (Real.exp 1 / Real.sqrt 2) by simpa
    apply Real.log_nonneg
    grw [one_le_div (by positivity), Real.sqrt_le_left (by positivity), ← Real.add_one_le_exp]
    norm_num
  set r := ((1 : ℝ) / (2 * (n + 1) + 1)) ^ 2 with hr
  have hr1 : r < 1 := by grw [hr, ← n.zero_le]; norm_num
  suffices HasSum (fun j ↦ r ^ (j + 1) / 3) ((1 : ℝ) / (12 * (n + 1 : ℕ) * ((n + 1 : ℕ) + 1))) by
    refine hasSum_le (fun j ↦ ?_) (log_stirlingSeq_sdiff_hasSum n) this
    simpa [hr, field] using show (3 : ℝ) ≤ 2 * (j + 1) + 1 by grind
  grind [((hasSum_geometric_of_lt_one (by positivity) hr1).mul_right r).div_const 3]


/-- For any `n`, we have `log_stirlingSeq 1 - log_stirlingSeq n ≤ 12⁻¹`. -/
theorem log_stirlingSeq_bounded_aux (n : ℕ) :
    log (stirlingSeq 1) - log (stirlingSeq (n + 1)) ≤ 12⁻¹ := by
  let f (k : ℕ) : ℝ := log (stirlingSeq (k + 1))
  let g (k : ℕ) : ℝ := 1 / (12 * (k + 1))
  have hf k (hk : k ∈ range n) : f k - (f (k + 1)) ≤ g k - g (k + 1) := by
    grw [log_stirlingSeq_sdiff_le]
    simp [field]
  replace hf := Finset.sum_le_sum hf
  rw [Finset.sum_range_sub', Finset.sum_range_sub'] at hf
  simp only [f, g, zero_add] at hf
  grw [hf]
  simp
  grind

/-- The sequence `log_stirlingSeq` is bounded below for `n ≥ 1`. -/
theorem log_stirlingSeq_bounded_by_constant (n : ℕ) :
    1 - 12⁻¹ - log 2 / 2 ≤ log (stirlingSeq (n + 1)) := by
  have := log_stirlingSeq_bounded_aux n
  rw [stirlingSeq_one, log_div (by positivity), log_exp, log_sqrt] at this <;> grind

/-- The sequence `stirlingSeq` is positive for `n > 0`. -/
theorem stirlingSeq'_pos (n : ℕ) : 0 < stirlingSeq (n + 1) := by unfold stirlingSeq; positivity

/-- The sequence `stirlingSeq` has a positive lower bound. -/
theorem stirlingSeq'_bounded_by_pos_constant : ∃ a, 0 < a ∧ ∀ n : ℕ, a ≤ stirlingSeq (n + 1) := by
  let c := 1 - 12⁻¹ - log 2 / 2
  have h := log_stirlingSeq_bounded_by_constant
  refine ⟨exp c, exp_pos _, fun n => ?_⟩
  rw [← le_log_iff_exp_le (stirlingSeq'_pos n)]
  exact h n

/-- The sequence `stirlingSeq ∘ succ` is monotone decreasing -/
theorem stirlingSeq'_antitone : Antitone (stirlingSeq ∘ succ) := fun n m h =>
  (log_le_log_iff (stirlingSeq'_pos m) (stirlingSeq'_pos n)).mp (log_stirlingSeq'_antitone h)

/-- The limit `a` of the sequence `stirlingSeq` satisfies `0 < a` -/
theorem stirlingSeq_has_pos_limit_a : ∃ a : ℝ, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a) := by
  obtain ⟨x, x_pos, hx⟩ := stirlingSeq'_bounded_by_pos_constant
  have hx' : x ∈ lowerBounds (Set.range (stirlingSeq ∘ succ)) := by simpa [lowerBounds] using hx
  refine ⟨_, lt_of_lt_of_le x_pos (le_csInf (Set.range_nonempty _) hx'), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact tendsto_atTop_ciInf stirlingSeq'_antitone ⟨x, hx'⟩


end OddPiPowers.StirlingLogCore
