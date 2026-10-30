module

public import OddPiPowers.Arithmetic.ActualPrimeDivisorRates
public import OddPiPowers.Arithmetic.PrimeRateCalibration
public import OddPiPowers.Arithmetic.TwelveLayerFamily
public import OddPiPowers.Arithmetic.ScaledPrimeRates

@[expose] public section

namespace OddPiPowers.PrimeRates

/-- The exact lcm used in the auxiliary denominators has normalized log rate 1. -/
theorem log_intervalLcm_div_tendsto :
    Filter.Tendsto (fun N : ℕ => Real.log (intervalLcm N : ℝ) / N)
      Filter.atTop (nhds 1) :=
  log_lcmUpto_div_tendsto

/-- A completely instantiated, unconditional positive divisor rate for the
17-interval twelve-layer family. Larger finite selections use the general
`twelveLayer_actualDivisor_eventually_exp_lower` interface. -/
theorem twelveLayerActualFamily_eventually_exp_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (((2 : ℝ) / 69 - η) * (69 * N : ℕ)) ≤
        ((twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor : ℝ) := by
  filter_upwards [calibration_primeCertificate_eventually_exp_lower hη] with N hN
  have hd : primeCertificate 69 N twelveLayerLowerBound ∣
      (twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor := by
    change primeCertificate twelveLayerShape.L N twelveLayerLowerBound ∣ _
    rw [primeCertificate_eq_grouping_certificate (twelveLayerActualGrouping N) twelveLayerLowerBound]
    exact (twelveLayerActualGrouping N).piCertificate_dvd_actualDivisor
      twelveLayerLowerBound twelveLayerLowerBound_le_cost
  have hle := Nat.le_of_dvd (twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor_pos hd
  exact hN.trans (by exact_mod_cast hle)

end OddPiPowers.PrimeRates

end
