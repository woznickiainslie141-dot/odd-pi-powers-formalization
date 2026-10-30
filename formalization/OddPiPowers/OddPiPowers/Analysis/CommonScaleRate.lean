module

public import OddPiPowers.Analysis.FactorialLogRate
public import OddPiPowers.Analysis.ActualCentralBound
public import OddPiPowers.Arithmetic.TwelveLayerPrimeRates

/-! The exact common normalization has logarithmic rate M-1. -/

@[expose] public section

namespace OddPiPowers

open Filter
open scoped Topology

theorem log_auxiliaryCommonScale (M n : ℕ) :
    Real.log (((auxiliaryCommonScale M n : ℚ) : ℝ)) =
      Real.log (Nat.factorial (M - 1) : ℝ) +
        ((M - 1 : ℕ) : ℝ) * Real.log (intervalLcm n : ℝ) := by
  unfold auxiliaryCommonScale
  push_cast
  rw [Real.log_mul (by exact_mod_cast Nat.factorial_ne_zero (M - 1))
      (pow_ne_zero _ (by exact_mod_cast (intervalLcm_pos n).ne')), Real.log_pow]

theorem log_auxiliaryCommonScale_div_tendsto (M : ℕ) :
    Tendsto (fun n : ℕ => Real.log (((auxiliaryCommonScale M n : ℚ) : ℝ)) / n)
      atTop (𝓝 ((M - 1 : ℕ) : ℝ)) := by
  have ht := (tendsto_const_div_atTop_nhds_zero_nat
    (Real.log (Nat.factorial (M - 1) : ℝ))).add
      (PrimeRates.log_intervalLcm_div_tendsto.const_mul ((M - 1 : ℕ) : ℝ))
  simpa only [zero_add, mul_one, log_auxiliaryCommonScale, add_div, mul_div_assoc] using ht

end OddPiPowers
