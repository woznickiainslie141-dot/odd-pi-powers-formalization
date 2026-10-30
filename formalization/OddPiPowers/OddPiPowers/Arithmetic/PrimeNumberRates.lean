module

import OddPiPowers.Vendor.PNT.Consequences
public import OddPiPowers.Arithmetic.PrimeWindowSums

@[expose] public section

open Filter Real Asymptotics
open scoped Topology BigOperators

namespace OddPiPowers.PrimeRates

/-- The theta form of the unconditional PNT, with the exact rate interface. -/
theorem theta_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) := by
  exact (isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        exact ne_of_gt hx)).mp chebyshev_asymptotic

/-- Psi, rather than theta, accounts for all prime powers in the lcm. -/
theorem psi_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
  exact (isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        exact ne_of_gt hx)).mp WeakPNT''

theorem log_lcmUpto_div_tendsto :
    Tendsto (fun N : ℕ => log (Nat.lcmUpto N : ℝ) / N) atTop (nhds 1) := by
  simpa only [Function.comp_def, Chebyshev.psi_eq_log_lcmUpto] using
    psi_ratio_tendsto.comp tendsto_natCast_atTop_atTop

theorem theta_scaled_div_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Chebyshev.theta ((N : ℝ) / c) / N)
      atTop (nhds (1 / c)) := by
  have h := (theta_ratio_tendsto.comp
    (tendsto_natCast_atTop_atTop.atTop_div_const hc)).div_const c
  convert h using 1
  simp only [Function.comp_def, div_div, div_mul_cancel₀ _ hc.ne']

theorem PrimeWindow.log_sum_div_tendsto (W : PrimeWindow) :
    Tendsto (fun N : ℕ => (∑ p ∈ W.primes N, log (p : ℝ)) / N)
      atTop (nhds (1 / W.lower - 1 / W.upper)) := by
  simpa only [W.sum_log_primes, sub_div] using
    (theta_scaled_div_tendsto W.lower_pos).sub (theta_scaled_div_tendsto W.upper_pos)

/-- Every finite collection is fixed before the limit; there is no exchange
of a prime-number-theorem limit and an infinite period sum here. -/
theorem finite_window_log_sum_div_tendsto {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) :
    Tendsto (fun N : ℕ =>
      (∑ i ∈ s, (W i).weight * ∑ p ∈ (W i).primes N, log (p : ℝ)) / N)
      atTop (nhds (∑ i ∈ s, (W i).weight * (1 / (W i).lower - 1 / (W i).upper))) := by
  have h := tendsto_finsetSum s (fun i hi =>
    ((W i).log_sum_div_tendsto).const_mul ((W i).weight : ℝ))
  simpa only [Finset.sum_div, mul_div_assoc] using h

end OddPiPowers.PrimeRates

end
