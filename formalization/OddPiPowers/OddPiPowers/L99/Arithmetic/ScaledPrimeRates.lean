module

public import OddPiPowers.Arithmetic.ScaledPrimeRates
public import OddPiPowers.L99.Arithmetic.CellPrimeWindows

@[expose] public section
open scoped BigOperators Topology
namespace OddPiPowers.L99.PrimeRates

open OddPiPowers.PrimeRates
theorem twentyEightLayer_scaled_actualDivisor_eventually_exp_lower {ι : Type*}
    (s : Finset ι) (V : ι → CertifiedCellWindow)
    (hinj : Set.InjOn (fun i => ((V i).period, (V i).cell)) ↑s)
    (hcap : ∀ i ∈ s, 1 ≤ (99 : ℝ) * (V i).toWindow.lower)
    (u : ℕ) {M : ℕ} (P : ℕ → ActualIntervals M)
    (G : ∀ N, ActualIntervals.ActualCarryGrouping (P N) (twentyEightLayerShape.scaleWeights u) N)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (((u : ℝ) * finiteWindowRate s (fun i => (V i).toWindow) 99 - η) * (99 * N : ℕ)) ≤
        ((P N).actualAuxiliaryPrimeDivisor : ℝ) := by
  have hB (z : ℝ) : windowWeightSum s (fun i => (V i).toWindow.scaleWeight u) z ≤
      u * twentyEightLayerLowerBound z := by
    rw [windowWeightSum_scaleWeight]
    exact Nat.mul_le_mul_left u (certifiedCellWindows_sum_le s V hinj z)
  have hshape : (twentyEightLayerShape.scaleWeights u).L = 99 := rfl
  have h := actualDivisor_eventually_exp_lower s (fun i => (V i).toWindow.scaleWeight u)
    (twentyEightLayerShape.scaleWeights u) (by rw [hshape]; decide) P G
    (fun z => u * twentyEightLayerLowerBound z)
    (twentyEightLayerLowerBound_scale_le_cost u) hcap hB hη
  simpa only [finiteWindowRate_scaleWeight, hshape] using h

end OddPiPowers.L99.PrimeRates

end
