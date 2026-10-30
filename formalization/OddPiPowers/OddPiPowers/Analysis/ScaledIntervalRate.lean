module

public import OddPiPowers.Analysis.FactorialLogRate
public import OddPiPowers.Analysis.CentralLogLipschitz
public import OddPiPowers.Analysis.ScaledGridLimit

/-! The central logarithmic rate of one actual scaled symmetric interval. -/

@[expose] public section

namespace OddPiPowers

open Filter MeasureTheory
open scoped Topology BigOperators

theorem scaled_interval_log_rate (L a : ℕ) (hL : 0 < L) (ha : 2 * a < L)
    (Y : ℝ) (hY : 0 < Y) :
    Tendsto (fun N : ℕ =>
      (Real.log (((L - 2 * a) * N).factorial : ℝ) -
        (((L - 2 * a) * N + 1 : ℕ) : ℝ) * Real.log ((L * N : ℕ) : ℝ) -
          ∑ r ∈ Finset.Icc (a * N) ((L - a) * N),
            centralLogIntegrand Y ((r : ℝ) / ((L * N : ℕ) : ℝ) - 1 / 2)) /
              ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (-centralIntervalRate (((L - 2 * a : ℕ) : ℝ) / L) Y)) := by
  have hab : a ≤ L - a := by omega
  have hk : 0 < L - 2 * a := by omega
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have haL : a ≤ L := by omega
  have h2aL : 2 * a ≤ L := by omega
  have hsum := scaled_grid_Icc_tendsto (centralLogIntegrand_continuous Y hY) (1 / Y)
    (by positivity) (centralLogIntegrand_lipschitz Y hY) L a (L - a) hL hab (-(1 / 2 : ℝ))
  have heL : (a : ℝ) / L + -(1 / 2) = -((((L - 2 * a : ℕ) : ℝ) / L) / 2) := by
    rw [Nat.cast_sub h2aL]
    push_cast
    field_simp
    ring
  have heR : ((L - a : ℕ) : ℝ) / L + -(1 / 2) = (((L - 2 * a : ℕ) : ℝ) / L) / 2 := by
    rw [Nat.cast_sub haL, Nat.cast_sub h2aL]
    push_cast
    field_simp
    ring
  rw [heL, heR] at hsum
  simp only [← sub_eq_add_neg] at hsum
  have hf := scaled_log_factorial_rate L (L - 2 * a) hL hk
  have ht := (hf.sub (scaled_log_div_tendsto_zero L hL)).sub hsum
  have hc : 0 ≤ ((L - 2 * a : ℕ) : ℝ) / L := by positivity
  have hi := centralIntervalRate_eq_integral (((L - 2 * a : ℕ) : ℝ) / L) Y hc hY
  have hi' : centralIntervalRate (((L - 2 * a : ℕ) : ℝ) / L) Y =
      (∫ u : ℝ in -((((L - 2 * a : ℕ) : ℝ) / L) / 2)..
        ((((L - 2 * a : ℕ) : ℝ) / L) / 2), centralLogIntegrand Y u) +
          (((L - 2 * a : ℕ) : ℝ) / L) -
            (((L - 2 * a : ℕ) : ℝ) / L) * Real.log (((L - 2 * a : ℕ) : ℝ) / L) := by
    simpa only [centralLogIntegrand] using hi
  convert ht using 1
  · funext N
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  · congr 1
    rw [hi']
    ring

end OddPiPowers
