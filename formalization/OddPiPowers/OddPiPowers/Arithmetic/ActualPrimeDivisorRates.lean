module

public import OddPiPowers.Arithmetic.PrimeDivisorRates
public import OddPiPowers.Arithmetic.CellPrimeWindows
public import OddPiPowers.Arithmetic.TwelveLayerActualDivisor

@[expose] public section

open scoped Topology BigOperators
open Filter Real

namespace OddPiPowers.PrimeRates

theorem primeCertificate_eq_grouping_certificate {M : ℕ} {P : ActualIntervals M}
    {C : CarryShape} {N : ℕ} (G : ActualIntervals.ActualCarryGrouping P C N)
    (B : ℝ → ℕ) : primeCertificate C.L N B = G.piCertificate B := by
  unfold primeCertificate ActualIntervals.ActualCarryGrouping.piCertificate
  rw [G.n_eq]
  rfl

/-- The asymptotic lower bound is for the actual common coefficient divisor,
for every grouped realization, not for a surrogate formal product. -/
theorem actualDivisor_eventually_exp_lower {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) {M : ℕ} (C : CarryShape) (hL : 0 < C.L)
    (P : ℕ → ActualIntervals M)
    (G : ∀ N, ActualIntervals.ActualCarryGrouping (P N) C N)
    (B : ℝ → ℕ) (hBcarry : ∀ z y, B z ≤ C.cost z y)
    (hcap : ∀ i ∈ s, 1 ≤ (C.L : ℝ) * (W i).lower)
    (hBwindow : ∀ z, windowWeightSum s W z ≤ B z) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      exp ((finiteWindowRate s W C.L - η) * (C.L * N : ℕ)) ≤
        ((P N).actualAuxiliaryPrimeDivisor : ℝ) := by
  apply divisor_eventually_exp_lower s W C.L hL B hcap hBwindow
    (fun N => (P N).actualAuxiliaryPrimeDivisor)
    (fun N => (P N).actualAuxiliaryPrimeDivisor_pos)
  · intro N
    rw [primeCertificate_eq_grouping_certificate (G N) B]
    exact (G N).piCertificate_dvd_actualDivisor B hBcarry
  · exact hη

theorem twelveLayer_actualDivisor_eventually_exp_lower {ι : Type*}
    (s : Finset ι) (V : ι → CertifiedCellWindow)
    (hinj : Set.InjOn (fun i => ((V i).period, (V i).cell)) ↑s)
    (hcap : ∀ i ∈ s, 1 ≤ (69 : ℝ) * (V i).toWindow.lower)
    {M : ℕ} (P : ℕ → ActualIntervals M)
    (G : ∀ N, ActualIntervals.ActualCarryGrouping (P N) twelveLayerShape N)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      exp ((finiteWindowRate s (fun i => (V i).toWindow) 69 - η) * (69 * N : ℕ)) ≤
        ((P N).actualAuxiliaryPrimeDivisor : ℝ) := by
  exact actualDivisor_eventually_exp_lower s _ twelveLayerShape (by decide)
    P G twelveLayerLowerBound twelveLayerLowerBound_le_cost hcap
    (certifiedCellWindows_sum_le s V hinj) hη

end OddPiPowers.PrimeRates

end
