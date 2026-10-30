module

public import OddPiPowers.Arithmetic.ActualPrimeDivisorRates

@[expose] public section

open scoped BigOperators Topology

namespace OddPiPowers.PrimeRates

def PrimeWindow.scaleWeight (u : ℕ) (W : PrimeWindow) : PrimeWindow :=
  { W with weight := u * W.weight }

theorem windowWeightSum_scaleWeight {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (u : ℕ) (z : ℝ) :
    windowWeightSum s (fun i => (W i).scaleWeight u) z = u * windowWeightSum s W z := by
  classical
  unfold windowWeightSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (if (W i).lower ≤ z ∧ z < (W i).upper then u * (W i).weight else 0) =
    u * (if (W i).lower ≤ z ∧ z < (W i).upper then (W i).weight else 0)
  split_ifs <;> simp

theorem finiteWindowRate_scaleWeight {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (L u : ℕ) :
    finiteWindowRate s (fun i => (W i).scaleWeight u) L = (u : ℝ) * finiteWindowRate s W L := by
  simp only [finiteWindowRate, PrimeWindow.scaleWeight, Nat.cast_mul, mul_assoc,
    ← Finset.mul_sum, mul_div_assoc]

theorem twelveLayer_scaled_actualDivisor_eventually_exp_lower {ι : Type*}
    (s : Finset ι) (V : ι → CertifiedCellWindow)
    (hinj : Set.InjOn (fun i => ((V i).period, (V i).cell)) ↑s)
    (hcap : ∀ i ∈ s, 1 ≤ (69 : ℝ) * (V i).toWindow.lower)
    (u : ℕ) {M : ℕ} (P : ℕ → ActualIntervals M)
    (G : ∀ N, ActualIntervals.ActualCarryGrouping (P N) (twelveLayerShape.scaleWeights u) N)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (((u : ℝ) * finiteWindowRate s (fun i => (V i).toWindow) 69 - η) * (69 * N : ℕ)) ≤
        ((P N).actualAuxiliaryPrimeDivisor : ℝ) := by
  have hB (z : ℝ) : windowWeightSum s (fun i => (V i).toWindow.scaleWeight u) z ≤
      u * twelveLayerLowerBound z := by
    rw [windowWeightSum_scaleWeight]
    exact Nat.mul_le_mul_left u (certifiedCellWindows_sum_le s V hinj z)
  have hshape : (twelveLayerShape.scaleWeights u).L = 69 := rfl
  have h := actualDivisor_eventually_exp_lower s (fun i => (V i).toWindow.scaleWeight u)
    (twelveLayerShape.scaleWeights u) (by rw [hshape]; decide) P G
    (fun z => u * twelveLayerLowerBound z)
    (twelveLayerLowerBound_scale_le_cost u) hcap hB hη
  simpa only [finiteWindowRate_scaleWeight, hshape] using h

end OddPiPowers.PrimeRates

end
