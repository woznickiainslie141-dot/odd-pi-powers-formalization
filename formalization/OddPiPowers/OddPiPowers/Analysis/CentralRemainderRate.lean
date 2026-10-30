module

public import OddPiPowers.Analysis.ActualCentralRate
public import OddPiPowers.Analysis.CommonScaleRate
public import OddPiPowers.Analysis.ReducedCentralBound

/-! A uniform actual remainder rate, obtained from the finite central bound. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

open Filter
open scoped Topology BigOperators

variable {M : ℕ}

theorem centralRemainderBound_log_rate (P : ℕ → ActualIntervals M)
    (L : ℕ) (hL : 0 < L) (A : Fin M → ℕ) (hA : ∀ a, 2 * A a < L)
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (m h : ℕ) (theta Y : ℝ) (hY : 1 / 2 < Y) :
    Tendsto (fun N : ℕ => Real.log ((P N).centralRemainderBound m h theta Y) /
      ((L * N : ℕ) : ℝ)) atTop (𝓝 (
        ((M - 1 : ℕ) : ℝ) + |theta| * Y -
          ∑ a : Fin M, centralIntervalRate (((L - 2 * A a : ℕ) : ℝ) / L) Y)) := by
  have hscale : Tendsto (fun N : ℕ => L * N) atTop atTop := tendsto_id.const_mul_atTop' hL
  have hS := (log_auxiliaryCommonScale_div_tendsto M).comp hscale
  have hC := (tendsto_const_div_atTop_nhds_zero_nat
    (Real.log (horizontalMajorantConstant (horizontalB Y) (Y + 1 / 2) m))).comp hscale
  have hlog := (scaled_log_div_tendsto_zero L hL).const_mul ((h + 1 : ℕ) : ℝ)
  have hcenter := centralLogRatio_scaled_tendsto P L hL A hA hn hl Y (by linarith)
  have htheta : Tendsto (fun N : ℕ => |theta| * (((L * N : ℕ) : ℝ) * Y) /
      ((L * N : ℕ) : ℝ)) atTop (𝓝 (|theta| * Y)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hn0 : (((L * N : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hL hN).ne'
    field_simp
  have ht := (((hS.add hC).add hlog).add htheta).add hcenter
  have ht' : Tendsto (fun N : ℕ =>
      Real.log (((auxiliaryCommonScale M (L * N) : ℚ) : ℝ)) / ((L * N : ℕ) : ℝ) +
        Real.log (horizontalMajorantConstant (horizontalB Y) (Y + 1 / 2) m) / ((L * N : ℕ) : ℝ) +
          ((h + 1 : ℕ) : ℝ) * (Real.log ((L * N : ℕ) : ℝ) / ((L * N : ℕ) : ℝ)) +
            |theta| * (((L * N : ℕ) : ℝ) * Y) / ((L * N : ℕ) : ℝ) +
              (P N).centralLogRatio Y / ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (((M - 1 : ℕ) : ℝ) + |theta| * Y -
          ∑ a : Fin M, centralIntervalRate (((L - 2 * A a : ℕ) : ℝ) / L) Y)) := by
    simpa only [Function.comp_def, add_zero, mul_zero, zero_add, sub_eq_add_neg] using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hnP : 0 < (P N).n := by rw [hn]; exact Nat.mul_pos hL hN
  rw [(P N).log_centralRemainderBound hnP m h theta Y hY, hn]
  ring

theorem actualRows_eventually_exp_upper (P : ℕ → ActualIntervals M)
    (hM : 0 < M) (L : ℕ) (hL : 0 < L) (A : Fin M → ℕ) (hA : ∀ a, 2 * A a < L)
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (hdegree : ∀ᶠ N : ℕ in atTop, 2 * ((M - 1) + 2) ≤ (P N).denominator.natDegree)
    (Y : ℝ) (hY : 1 / 2 < Y) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ h : Fin M,
      ‖∑ j : Fin M, (actualAuxiliary (P N) h j).eval₂ (Rat.castHom ℂ) Complex.I * lambda ^ j.val‖ ≤
        Real.exp (((M - 1 : ℕ) + (Real.pi / 2) * Y -
          ∑ a : Fin M, centralIntervalRate (((L - 2 * A a : ℕ) : ℝ) / L) Y + η) *
            ((L * N : ℕ) : ℝ)) := by
  let rate : ℝ := ((M - 1 : ℕ) : ℝ) + (Real.pi / 2) * Y -
    ∑ a : Fin M, centralIntervalRate (((L - 2 * A a : ℕ) : ℝ) / L) Y
  have ht := centralRemainderBound_log_rate P L hL A hA hn hl (M - 1) (M - 1)
    (Real.pi / 2) Y hY
  rw [abs_of_pos (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))] at ht
  have hnear : ∀ᶠ N : ℕ in atTop,
      Real.log ((P N).centralRemainderBound (M - 1) (M - 1) (Real.pi / 2) Y) /
        ((L * N : ℕ) : ℝ) < rate + η := ht.eventually (gt_mem_nhds (by dsimp [rate]; linarith))
  filter_upwards [hnear, hdegree, eventually_gt_atTop (0 : ℕ)] with N hnear hd hN h
  have hnP : 0 < (P N).n := by rw [hn]; exact Nat.mul_pos hL hN
  have hnR : (0 : ℝ) < ((L * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hL hN
  have hlog := (div_lt_iff₀ hnR).mp hnear
  calc
    _ ≤ (P N).centralRemainderBound (M - 1) (M - 1) (Real.pi / 2) Y :=
      actualAuxiliaryAtI_norm_le_central (P N) h hM hnP Y hY (M - 1) (by omega) hd
    _ = Real.exp (Real.log ((P N).centralRemainderBound (M - 1) (M - 1) (Real.pi / 2) Y)) :=
      (Real.exp_log ((P N).centralRemainderBound_pos hnP _ _ _ _ hY)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog.le

end OddPiPowers.ActualIntervals
