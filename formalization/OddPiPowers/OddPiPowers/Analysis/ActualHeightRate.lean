module

public import OddPiPowers.Analysis.ActualValueHeight
public import OddPiPowers.Analysis.BalancedHeightRate
public import OddPiPowers.Analysis.ActualCentralRate

/-! The general height has exactly the expected exponential rate. -/

@[expose] public section

namespace OddPiPowers

open Filter
open scoped Topology BigOperators

variable {M : ℕ}

noncomputable def actualHeightConstant (M : ℕ) : ℚ :=
  (Nat.factorial (M - 1) : ℚ) * ((2 * M + 2 * (M - 1) + 1 : ℕ) : ℚ) ^ (M - 1)

theorem actualHeightConstant_pos (M : ℕ) : 0 < actualHeightConstant M := by
  have hf : (0 : ℚ) < Nat.factorial (M - 1) := by exact_mod_cast Nat.factorial_pos (M - 1)
  unfold actualHeightConstant
  positivity

theorem log_actualValueMajorant (P : ActualIntervals M) :
    Real.log (((actualValueMajorant P : ℚ) : ℝ)) =
      Real.log (((actualHeightConstant M : ℚ) : ℝ)) +
        ((M - 1 : ℕ) : ℝ) * Real.log (intervalLcm P.n : ℝ) +
          ((2 * (M - 1) + M + 1 : ℕ) : ℝ) * Real.log ((P.n : ℝ) + 1) +
            ((∑ a : Fin M, P.length a : ℕ) : ℝ) * Real.log 2 := by
  have hK : (0 : ℝ) < ((actualHeightConstant M : ℚ) : ℝ) := by
    exact_mod_cast actualHeightConstant_pos M
  have hd : (0 : ℝ) < intervalLcm P.n := by exact_mod_cast intervalLcm_pos P.n
  have he : ((actualValueMajorant P : ℚ) : ℝ) =
      (((actualHeightConstant M : ℚ) : ℝ) * (intervalLcm P.n : ℝ) ^ (M - 1) *
        ((P.n : ℝ) + 1) ^ (2 * (M - 1) + M + 1) *
          (2 : ℝ) ^ (∑ a : Fin M, P.length a)) := by
    rw [actualValueMajorant_factorization]
    unfold actualHeightConstant
    push_cast
    rfl
  rw [he, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul hK.ne' (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]

noncomputable def shapeRelativeLength (L : ℕ) (A : Fin M → ℕ) : ℝ :=
  ∑ a : Fin M, (((L - 2 * A a : ℕ) : ℝ) / L)

theorem sum_scaled_lengths (P : ℕ → ActualIntervals M) (L : ℕ) (A : Fin M → ℕ)
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N) (N : ℕ) :
    (∑ a : Fin M, (P N).length a) = (∑ a : Fin M, (L - 2 * A a)) * N := by
  simp_rw [ActualIntervals.scaled_length P L A hn hl]
  exact (Finset.sum_mul _ _ _).symm

theorem actualValueMajorant_log_rate (P : ℕ → ActualIntervals M)
    (L : ℕ) (hL : 0 < L) (A : Fin M → ℕ)
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N) :
    Tendsto (fun N : ℕ => Real.log (((actualValueMajorant (P N) : ℚ) : ℝ)) /
      ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (((M - 1 : ℕ) : ℝ) + shapeRelativeLength L A * Real.log 2)) := by
  have hscale : Tendsto (fun N : ℕ => L * N) atTop atTop := tendsto_id.const_mul_atTop' hL
  have hK := (tendsto_const_div_atTop_nhds_zero_nat
    (Real.log (((actualHeightConstant M : ℚ) : ℝ)))).comp hscale
  have hd := (PrimeRates.log_intervalLcm_div_tendsto.comp hscale).const_mul ((M - 1 : ℕ) : ℝ)
  have hp := (log_nat_succ_div_nat_tendsto_zero.comp hscale).const_mul
    ((2 * (M - 1) + M + 1 : ℕ) : ℝ)
  have hrel : shapeRelativeLength L A = ((∑ a : Fin M, ((L - 2 * A a) : ℕ)) : ℝ) / L := by
    simp only [shapeRelativeLength, Nat.cast_sum, Finset.sum_div]
  have hpow : Tendsto (fun N : ℕ => ((∑ a : Fin M, (P N).length a : ℕ) : ℝ) *
      Real.log 2 / ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (shapeRelativeLength L A * Real.log 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [sum_scaled_lengths P L A hn hl, hrel]
    push_cast
    field_simp
  have ht := ((hK.add hd).add hp).add hpow
  simp only [zero_add, mul_one, mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [] with N
  rw [log_actualValueMajorant, hn]
  simp only [Function.comp_def]
  ring

theorem actualConstantHeight_eventually_exp (P : ℕ → ActualIntervals M)
    (L : ℕ) (hL : 0 < L) (A : Fin M → ℕ)
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (C : ℝ) (hC : 0 < C) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, C * ((actualValueMajorant (P N) : ℚ) : ℝ) ≤
      Real.exp ((((M - 1 : ℕ) : ℝ) + shapeRelativeLength L A * Real.log 2 + η) *
        ((L * N : ℕ) : ℝ)) := by
  let G := ((M - 1 : ℕ) : ℝ) + shapeRelativeLength L A * Real.log 2
  have hscale : Tendsto (fun N : ℕ => L * N) atTop atTop := tendsto_id.const_mul_atTop' hL
  have ht := ((tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).comp hscale).add
    (actualValueMajorant_log_rate P L hL A hn hl)
  simp only [zero_add] at ht
  have hnear : ∀ᶠ N : ℕ in atTop,
      Real.log C / ((L * N : ℕ) : ℝ) +
        Real.log (((actualValueMajorant (P N) : ℚ) : ℝ)) / ((L * N : ℕ) : ℝ) < G + η :=
    ht.eventually (gt_mem_nhds (by dsimp [G]; linarith))
  filter_upwards [hnear, eventually_gt_atTop (0 : ℕ)] with N hnear hN
  have hnR : (0 : ℝ) < ((L * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hL hN
  have hV : (0 : ℝ) < ((actualValueMajorant (P N) : ℚ) : ℝ) := by
    exact_mod_cast actualValueMajorant_pos (P N)
  have he : (Real.log C + Real.log (((actualValueMajorant (P N) : ℚ) : ℝ))) /
      ((L * N : ℕ) : ℝ) < G + η := by simpa only [add_div, Function.comp_def] using hnear
  rw [← Real.log_mul hC.ne' hV.ne'] at he
  have hmul := (div_lt_iff₀ hnR).mp he
  calc
    _ = Real.exp (Real.log (C * ((actualValueMajorant (P N) : ℚ) : ℝ))) :=
      (Real.exp_log (mul_pos hC hV)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hmul.le

end OddPiPowers
