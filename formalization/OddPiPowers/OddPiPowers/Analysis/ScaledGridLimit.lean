module

public import OddPiPowers.Analysis.GridIntegralBound
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Riemann sums along the actual integer multiples, including the extra endpoint. -/

@[expose] public section

namespace OddPiPowers

open Filter MeasureTheory
open scoped Topology BigOperators

theorem scaled_grid_Ico_tendsto {f : ℝ → ℝ} (hf : Continuous f) (K : ℝ)
    (hK : 0 ≤ K) (hLip : ∀ x y, ‖f x - f y‖ ≤ K * |x - y|)
    (L a b : ℕ) (hL : 0 < L) (hab : a ≤ b) (s : ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ r ∈ Finset.Ico (a * N) (b * N), f ((r : ℝ) / ((L * N : ℕ) : ℝ) + s)) /
        ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (∫ x : ℝ in (a : ℝ) / L + s..(b : ℝ) / L + s, f x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz := tendsto_const_div_atTop_nhds_zero_nat
    (K * ((b - a : ℕ) : ℝ) / (L : ℝ) ^ 2)
  apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_ hz
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn : (0 : ℝ) < ((L * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hL hN
  have hquot (k : ℕ) : ((k * N : ℕ) : ℝ) / ((L * N : ℕ) : ℝ) = (k : ℝ) / L := by
    push_cast
    field_simp
  have hg := grid_integral_error hf K hK hLip s (1 / ((L * N : ℕ) : ℝ))
    (by positivity) (a * N) (b * N) (Nat.mul_le_mul_right N hab)
  have hpoint (k : ℕ) : (k : ℝ) * (1 / ((L * N : ℕ) : ℝ)) + s =
      (k : ℝ) / ((L * N : ℕ) : ℝ) + s := by ring
  simp_rw [hpoint] at hg
  rw [hquot a, hquot b] at hg
  calc
    _ = ‖(1 / ((L * N : ℕ) : ℝ)) *
        (∑ r ∈ Finset.Ico (a * N) (b * N), f ((r : ℝ) / ((L * N : ℕ) : ℝ) + s)) -
          ∫ x : ℝ in (a : ℝ) / L + s..(b : ℝ) / L + s, f x‖ := by congr 1; ring
    _ ≤ _ := hg
    _ = _ := by
      rw [← Nat.sub_mul]
      push_cast
      field_simp

theorem scaled_grid_Icc_tendsto {f : ℝ → ℝ} (hf : Continuous f) (K : ℝ)
    (hK : 0 ≤ K) (hLip : ∀ x y, ‖f x - f y‖ ≤ K * |x - y|)
    (L a b : ℕ) (hL : 0 < L) (hab : a ≤ b) (s : ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ r ∈ Finset.Icc (a * N) (b * N), f ((r : ℝ) / ((L * N : ℕ) : ℝ) + s)) /
        ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (∫ x : ℝ in (a : ℝ) / L + s..(b : ℝ) / L + s, f x)) := by
  have hscale : Tendsto (fun N : ℕ => L * N) atTop atTop := tendsto_id.const_mul_atTop' hL
  have hz := (tendsto_const_div_atTop_nhds_zero_nat (f ((b : ℝ) / L + s))).comp hscale
  have ht := (scaled_grid_Ico_tendsto hf K hK hLip L a b hL hab s).add hz
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpoint : ((b * N : ℕ) : ℝ) / ((L * N : ℕ) : ℝ) = (b : ℝ) / L := by
    push_cast
    field_simp
  rw [← Finset.sum_Ico_add_eq_sum_Icc (Nat.mul_le_mul_right N hab), add_div, hpoint]
  simp only [Function.comp_def]

end OddPiPowers
