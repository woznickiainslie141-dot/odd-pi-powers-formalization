module

public import OddPiPowers.Analysis.ScaledIntervalRate
public import OddPiPowers.Analysis.CentralLogProducts

/-! Central rates for actual families with fixed integer interval endpoints. -/

@[expose] public section

namespace OddPiPowers

open Filter
open scoped Topology BigOperators

namespace ActualIntervals

variable {M : ℕ}

theorem centralLogRatio_eq_interval_sum (P : ActualIntervals M) (hn : 0 < P.n)
    (Y : ℝ) (hY : Y ≠ 0) :
    P.centralLogRatio Y = ∑ a : Fin M,
      (Real.log (Nat.factorial (P.length a) : ℝ) -
        ((P.length a + 1 : ℕ) : ℝ) * Real.log (P.n : ℝ) -
          ∑ r ∈ P.interval a, centralLogIntegrand Y (P.horizontalOffset r)) := by
  rw [P.centralLogRatio_eq_finite_sum hn Y hY,
    P.totalMultiplicity_eq_sum_interval_card]
  simp_rw [P.interval_card_eq_length_add_one]
  push_cast
  simp only [Finset.sum_sub_distrib, Finset.sum_mul, centralLogIntegrand_eq, Finset.mul_sum]

theorem scaled_length (P : ℕ → ActualIntervals M) (L : ℕ) (A : Fin M → ℕ)
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (N : ℕ) (a : Fin M) : (P N).length a = (L - 2 * A a) * N := by
  rw [length, hn, hl, ← Nat.mul_assoc, ← Nat.sub_mul]

theorem scaled_interval (P : ℕ → ActualIntervals M) (L : ℕ) (A : Fin M → ℕ)
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (N : ℕ) (a : Fin M) :
    (P N).interval a = Finset.Icc (A a * N) ((L - A a) * N) := by
  rw [interval, right, hn, hl, ← Nat.sub_mul]

theorem centralLogRatio_scaled_tendsto (P : ℕ → ActualIntervals M)
    (L : ℕ) (hL : 0 < L) (A : Fin M → ℕ)
    (hA : ∀ a, 2 * A a < L) (hn : ∀ N, (P N).n = L * N)
    (hl : ∀ N a, (P N).left a = A a * N) (Y : ℝ) (hY : 0 < Y) :
    Tendsto (fun N : ℕ => (P N).centralLogRatio Y / ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (-∑ a : Fin M, centralIntervalRate (((L - 2 * A a : ℕ) : ℝ) / L) Y)) := by
  have ht := tendsto_finsetSum Finset.univ
    (fun a ha => scaled_interval_log_rate L (A a) hL (hA a) Y hY)
  have ht' : Tendsto (fun N : ℕ => ∑ a : Fin M,
      (Real.log (((L - 2 * A a) * N).factorial : ℝ) -
        (((L - 2 * A a) * N + 1 : ℕ) : ℝ) * Real.log ((L * N : ℕ) : ℝ) -
          ∑ r ∈ Finset.Icc (A a * N) ((L - A a) * N),
            centralLogIntegrand Y ((r : ℝ) / ((L * N : ℕ) : ℝ) - 1 / 2)) /
              ((L * N : ℕ) : ℝ)) atTop
      (𝓝 (-∑ a : Fin M, centralIntervalRate (((L - 2 * A a : ℕ) : ℝ) / L) Y)) := by
    simpa only [Finset.sum_neg_distrib] using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hnP : 0 < (P N).n := by rw [hn]; exact Nat.mul_pos hL hN
  rw [(P N).centralLogRatio_eq_interval_sum hnP Y hY.ne', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [scaled_length P L A hn hl, scaled_interval P L A hn hl, hn]
  simp only [horizontalOffset, hn]

end ActualIntervals
end OddPiPowers
