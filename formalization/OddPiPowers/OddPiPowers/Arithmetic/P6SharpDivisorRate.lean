module

public import OddPiPowers.Arithmetic.P6PeriodAggregate
public import OddPiPowers.Arithmetic.TwelveLayerDivisorCertificate

/-! A fixed rational rate for the actual s=11 coefficient divisor. -/

@[expose] public section

namespace OddPiPowers.PrimeRates

open Filter
open scoped Topology

theorem p6_finite_window_rate_lower :
    (4543599 / 1100000 : ℝ) ≤ periodWindowRate 1000000 selectedCellSet selectedCellTemplate := by
  have ht := selectedTemplateRate_ge_prefix_add_tail 32 1000000 (by norm_num) (by norm_num)
    (412848897248127 / 100000000000000) (205621482243 / 100000000000000)
    p6_prefix_floor_lower p6_tail_floor_lower
  apply le_trans _ ht
  norm_num [cellShrinkEpsilon]

theorem p6_actualDivisor_eventually_exp_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (((4543599 / 100000 : ℝ) - ε) * ((69 * N : ℕ) : ℝ)) ≤
        ((scaledTwelveLayerActualFamily 11 (by norm_num) N).actualAuxiliaryPrimeDivisor : ℝ) := by
  apply twelveLayer_actualDivisor_of_finite_rate 11 (by norm_num) 1000000
    (4543599 / 100000) _ hε
  have ht := p6_finite_window_rate_lower
  norm_num only [Nat.cast_ofNat]
  linarith

end OddPiPowers.PrimeRates
