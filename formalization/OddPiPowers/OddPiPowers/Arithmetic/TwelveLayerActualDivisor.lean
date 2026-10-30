module

public import OddPiPowers.Arithmetic.CertifiedPrimeDivisor
public import OddPiPowers.Arithmetic.TwelveLayerCertifiedBound

@[expose] public section

namespace OddPiPowers.ActualIntervals.ActualCarryGrouping

variable {M N : ℕ} {P : ActualIntervals M}

theorem twelveLayer_lowerBound_le_minimum
    (G : ActualCarryGrouping P twelveLayerShape N) (p : ℕ) (hp : 0 < p) :
    twelveLayerLowerBound (N / p) ≤ P.carryWeightMinimum p :=
  G.lowerBound_le_carryWeightMinimum twelveLayerLowerBound
    twelveLayerLowerBound_le_cost p hp

noncomputable def twelveLayerDivisor
    (G : ActualCarryGrouping P twelveLayerShape N) : ℕ :=
  G.piCertificate twelveLayerLowerBound

theorem twelveLayerDivisor_pos (G : ActualCarryGrouping P twelveLayerShape N) :
    0 < G.twelveLayerDivisor :=
  G.piCertificate_pos twelveLayerLowerBound

theorem twelveLayerDivisor_dvd_actualDivisor
    (G : ActualCarryGrouping P twelveLayerShape N) :
    G.twelveLayerDivisor ∣ P.actualAuxiliaryPrimeDivisor :=
  G.piCertificate_dvd_actualDivisor twelveLayerLowerBound twelveLayerLowerBound_le_cost

theorem twelveLayerDivisor_dvd_coeff
    (G : ActualCarryGrouping P twelveLayerShape N) (h j : Fin M) (k : ℕ) :
    (G.twelveLayerDivisor : ℤ) ∣ (actualAuxiliaryInt P h j).coeff k :=
  G.piCertificate_dvd_integerCoefficients twelveLayerLowerBound
    twelveLayerLowerBound_le_cost h j k

theorem twelveLayer_scaled_lowerBound_le_minimum (s : ℕ)
    (G : ActualCarryGrouping P (twelveLayerShape.scaleWeights s) N)
    (p : ℕ) (hp : 0 < p) :
    s * twelveLayerLowerBound (N / p) ≤ P.carryWeightMinimum p :=
  G.lowerBound_le_carryWeightMinimum (fun z => s * twelveLayerLowerBound z)
    (twelveLayerLowerBound_scale_le_cost s) p hp

noncomputable def twelveLayerScaledDivisor (s : ℕ)
    (G : ActualCarryGrouping P (twelveLayerShape.scaleWeights s) N) : ℕ :=
  G.piCertificate (fun z => s * twelveLayerLowerBound z)

theorem twelveLayerScaledDivisor_pos (s : ℕ)
    (G : ActualCarryGrouping P (twelveLayerShape.scaleWeights s) N) :
    0 < G.twelveLayerScaledDivisor s :=
  G.piCertificate_pos (fun z => s * twelveLayerLowerBound z)

theorem twelveLayerScaledDivisor_dvd_actualDivisor (s : ℕ)
    (G : ActualCarryGrouping P (twelveLayerShape.scaleWeights s) N) :
    G.twelveLayerScaledDivisor s ∣ P.actualAuxiliaryPrimeDivisor :=
  G.piCertificate_dvd_actualDivisor (fun z => s * twelveLayerLowerBound z)
    (twelveLayerLowerBound_scale_le_cost s)

theorem twelveLayerScaledDivisor_dvd_coeff (s : ℕ)
    (G : ActualCarryGrouping P (twelveLayerShape.scaleWeights s) N)
    (h j : Fin M) (k : ℕ) :
    (G.twelveLayerScaledDivisor s : ℤ) ∣ (actualAuxiliaryInt P h j).coeff k :=
  G.piCertificate_dvd_integerCoefficients (fun z => s * twelveLayerLowerBound z)
    (twelveLayerLowerBound_scale_le_cost s) h j k

end OddPiPowers.ActualIntervals.ActualCarryGrouping

end
