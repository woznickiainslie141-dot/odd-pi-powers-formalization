module
public import OddPiPowers.L99.Arithmetic.L99PeriodAggregate
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerDivisorCertificate
@[expose] public section
namespace OddPiPowers.L99.PrimeRates
open Filter
open scoped Topology

theorem l99_finite_window_rate_lower :
    (2761813 / 200000 : ℝ) ≤
      periodWindowRate 1000000 selectedCellSet selectedCellTemplate := by
  have ht := selectedTemplateRate_ge_prefix_add_tail 32 1000000 (by norm_num) (by norm_num)
    (1380525198339888 / 100000000000000) (381339545481 / 100000000000000)
    l99_prefix_floor_lower l99_tail_floor_lower
  apply le_trans _ ht
  norm_num [cellShrinkEpsilon]

theorem l99_actualDivisor_eventually_exp_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (((2761813 / 50000 : ℝ) - ε) * ((99 * N : ℕ) : ℝ)) ≤
        ((scaledTwentyEightLayerActualFamily 4 (by norm_num) N).actualAuxiliaryPrimeDivisor : ℝ) := by
  apply twentyEightLayer_actualDivisor_of_finite_rate 4 (by norm_num) 1000000
    (2761813 / 50000) _ hε
  have ht := l99_finite_window_rate_lower
  norm_num only [Nat.cast_ofNat]
  linarith

end OddPiPowers.L99.PrimeRates
