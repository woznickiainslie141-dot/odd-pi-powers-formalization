module

public import OddPiPowers.Analysis.StirlingLogCore
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Stirling logarithmic rates from the pinned positive-limit core. -/

@[expose] public section

namespace OddPiPowers

open Filter
open scoped Topology

theorem log_nat_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  simpa only [Function.comp_def, pow_one, one_mul, add_zero] using h

theorem log_factorial_sub_self_log_div_self_tendsto :
    Tendsto (fun n : ℕ =>
      (Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (𝓝 (-1)) := by
  obtain ⟨a, ha, hseq⟩ := StirlingLogCore.stirlingSeq_has_pos_limit_a
  have hlog := hseq.log (ne_of_gt ha)
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hseqzero : Tendsto (fun n : ℕ => Real.log (StirlingLogCore.stirlingSeq n) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hlog.mul hinv
  have htwozero : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
    have ht := log_nat_div_nat_tendsto_zero.add (hinv.const_mul (Real.log 2))
    simp only [mul_zero, zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0]
    ring
  have hlimit := (hseqzero.add (htwozero.const_mul (1 / 2 : ℝ))).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have heq : (fun n : ℕ =>
      (Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ))
      =ᶠ[atTop] (fun n : ℕ =>
        Real.log (StirlingLogCore.stirlingSeq n) / (n : ℝ) +
          (1 / 2 : ℝ) * (Real.log (2 * (n : ℝ)) / (n : ℝ)) - 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    have hs := StirlingLogCore.log_stirlingSeq_formula n
    rw [Real.log_div hn0 (ne_of_gt (Real.exp_pos 1)), Real.log_exp] at hs
    rw [mul_comm (2 : ℝ) (n : ℝ)] at hs
    field_simp [hn0]
    nlinarith [hs]
  have hc := hlimit.congr' heq.symm
  simpa using hc

theorem scaled_log_factorial_rate (L k : ℕ) (hL : 0 < L) (hk : 0 < k) :
    Tendsto (fun N : ℕ =>
      (Real.log ((k * N).factorial : ℝ) - (k * N : ℕ) *
        Real.log ((L * N : ℕ) : ℝ)) / ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (((k : ℝ) / (L : ℝ)) * Real.log ((k : ℝ) / (L : ℝ)) -
        ((k : ℝ) / (L : ℝ)))) := by
  have hscale : Tendsto (fun N : ℕ => k * N) atTop atTop :=
    tendsto_id.const_mul_atTop' hk
  have hbase := log_factorial_sub_self_log_div_self_tendsto.comp hscale
  have ht := (hbase.add_const (Real.log ((k : ℝ) / (L : ℝ)))).const_mul
    ((k : ℝ) / (L : ℝ))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have heq : (fun N : ℕ =>
      (Real.log ((k * N).factorial : ℝ) - (k * N : ℕ) *
        Real.log ((L * N : ℕ) : ℝ)) / ((L * N : ℕ) : ℝ))
      =ᶠ[atTop] (fun N : ℕ => ((k : ℝ) / (L : ℝ)) *
        ((Real.log ((k * N).factorial : ℝ) - ((k * N : ℕ) : ℝ) *
          Real.log ((k * N : ℕ) : ℝ)) / ((k * N : ℕ) : ℝ) +
            Real.log ((k : ℝ) / (L : ℝ)))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
    simp only [Nat.cast_mul]
    rw [Real.log_mul hk0 hN0, Real.log_mul hL0 hN0, Real.log_div hk0 hL0]
    field_simp [hk0, hL0, hN0]
    ring
  have hr := ht.congr' heq.symm
  convert hr using 1
  ring

theorem scaled_log_div_tendsto_zero (L : ℕ) (hL : 0 < L) :
    Tendsto (fun N : ℕ => Real.log ((L * N : ℕ) : ℝ) / ((L * N : ℕ) : ℝ))
      atTop (𝓝 0) :=
  log_nat_div_nat_tendsto_zero.comp (tendsto_id.const_mul_atTop' hL)

end OddPiPowers
