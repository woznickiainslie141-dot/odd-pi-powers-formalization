module

public import OddPiPowers.Analysis.BalancedValueHeight
public import OddPiPowers.Analysis.CommonScaleRate

/-! Uniform height rates; every polynomial loss is proved negligible. -/

@[expose] public section

namespace OddPiPowers

open Filter
open scoped Topology

theorem log_nat_succ_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have hl := log_nat_div_nat_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add 1
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have ht := hl.mul hr
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
  field_simp

noncomputable def balancedHeightConstant (M : ℕ) : ℚ :=
  (Nat.factorial (M - 1) : ℚ) * ((M + 2 * (M - 1) + 1 : ℕ) : ℚ) ^ (M - 1)

theorem balancedHeightConstant_pos (M : ℕ) : 0 < balancedHeightConstant M := by
  have hf : (0 : ℚ) < Nat.factorial (M - 1) := by exact_mod_cast Nat.factorial_pos (M - 1)
  unfold balancedHeightConstant
  positivity

theorem log_balancedValueMajorant (M n : ℕ) :
    Real.log (((balancedValueMajorant M n : ℚ) : ℝ)) =
      Real.log (((balancedHeightConstant M : ℚ) : ℝ)) +
        ((M - 1 : ℕ) : ℝ) * Real.log (intervalLcm n : ℝ) +
          ((2 * (M - 1) + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
            ((M * n : ℕ) : ℝ) * Real.log 2 := by
  have hK : (0 : ℝ) < ((balancedHeightConstant M : ℚ) : ℝ) := by
    exact_mod_cast balancedHeightConstant_pos M
  have hd : (0 : ℝ) < intervalLcm n := by exact_mod_cast intervalLcm_pos n
  have he : ((balancedValueMajorant M n : ℚ) : ℝ) =
      (((balancedHeightConstant M : ℚ) : ℝ) * (intervalLcm n : ℝ) ^ (M - 1) *
        ((n : ℝ) + 1) ^ (2 * (M - 1) + 1) * (2 : ℝ) ^ (M * n)) := by
    rw [balancedValueMajorant_factorization]
    unfold balancedHeightConstant
    push_cast
    rfl
  rw [he, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul hK.ne' (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]

theorem balancedValueMajorant_log_rate (M : ℕ) :
    Tendsto (fun n : ℕ => Real.log (((balancedValueMajorant M n : ℚ) : ℝ)) / n)
      atTop (𝓝 (((M - 1 : ℕ) : ℝ) + (M : ℝ) * Real.log 2)) := by
  have hK := tendsto_const_div_atTop_nhds_zero_nat
    (Real.log (((balancedHeightConstant M : ℚ) : ℝ)))
  have hd := PrimeRates.log_intervalLcm_div_tendsto.const_mul ((M - 1 : ℕ) : ℝ)
  have hp := log_nat_succ_div_nat_tendsto_zero.const_mul ((2 * (M - 1) + 1 : ℕ) : ℝ)
  have hpow : Tendsto (fun n : ℕ => ((M * n : ℕ) : ℝ) * Real.log 2 / n)
      atTop (𝓝 ((M : ℝ) * Real.log 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  have ht := ((hK.add hd).add hp).add hpow
  simp only [zero_add, mul_one, mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  rw [log_balancedValueMajorant]
  ring

theorem balancedConstantHeight_eventually_exp (M : ℕ) (C : ℝ) (hC : 0 < C)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, C * ((balancedValueMajorant M n : ℚ) : ℝ) ≤
      Real.exp ((((M - 1 : ℕ) : ℝ) + (M : ℝ) * Real.log 2 + η) * (n : ℝ)) := by
  let G : ℝ := ((M - 1 : ℕ) : ℝ) + (M : ℝ) * Real.log 2
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add
    (balancedValueMajorant_log_rate M)
  simp only [zero_add] at ht
  have hnear : ∀ᶠ n : ℕ in atTop,
      Real.log C / n + Real.log (((balancedValueMajorant M n : ℚ) : ℝ)) / n < G + η :=
    ht.eventually (gt_mem_nhds (by dsimp [G]; linarith))
  filter_upwards [hnear, eventually_gt_atTop (0 : ℕ)] with n hnear hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : (0 : ℝ) < ((balancedValueMajorant M n : ℚ) : ℝ) := by
    exact_mod_cast balancedValueMajorant_pos M n
  have he : (Real.log C + Real.log (((balancedValueMajorant M n : ℚ) : ℝ))) / n < G + η := by
    simpa only [add_div] using hnear
  rw [← Real.log_mul hC.ne' hV.ne'] at he
  have hmul := (div_lt_iff₀ hnR).mp he
  calc
    _ = Real.exp (Real.log (C * ((balancedValueMajorant M n : ℚ) : ℝ))) :=
      (Real.exp_log (mul_pos hC hV)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hmul.le

end OddPiPowers
