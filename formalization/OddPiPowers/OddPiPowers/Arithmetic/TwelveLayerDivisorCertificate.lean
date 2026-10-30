module

public import OddPiPowers.Arithmetic.CellWindowAggregate
public import OddPiPowers.Construction.ScaledTwelveLayerFamily

/-! A verified finite window rate applies to the actual scaled divisor. -/

@[expose] public section

namespace OddPiPowers.PrimeRates

open Filter
open scoped Topology

theorem twelveLayer_actualDivisor_of_finite_rate (s : ℕ) (hs : 0 < s)
    (K : ℕ) (g : ℝ)
    (hg : g ≤ (s : ℝ) * periodWindowRate K selectedCellSet selectedCellTemplate)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp ((g - ε) * ((69 * N : ℕ) : ℝ)) ≤
      ((scaledTwelveLayerActualFamily s hs N).actualAuxiliaryPrimeDivisor : ℝ) := by
  have ht := periodWindowFamily_scaled_actualDivisor_eventually_exp_lower K
    selectedCellSet selectedCellTemplate selectedCellTemplate_cell_inj
    (fun c hc => selectedCellTemplate_cap c) s
    (scaledTwelveLayerActualFamily s hs) (scaledTwelveLayerActualGrouping s hs) hε
  filter_upwards [ht] with N hN
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (sub_le_sub_right hg ε) (Nat.cast_nonneg _))).trans hN

end OddPiPowers.PrimeRates
