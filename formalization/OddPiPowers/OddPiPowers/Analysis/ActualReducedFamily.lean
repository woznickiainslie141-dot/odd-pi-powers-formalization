module

public import OddPiPowers.Analysis.ActualReducedRates

/-! The actual scaled interval construction supplies the complete transfer interface. -/

@[expose] public section

namespace OddPiPowers

open Filter Polynomial
open scoped Topology

noncomputable def actualReducedRows (m L : ℕ) (P : ℕ → ActualIntervals (m + 1))
    (n : ℕ) (h : Fin (m + 1)) : Polynomial GaussianInt :=
  reducedGaussianRow (P (n / L)) h

theorem actualReducedRows_at_scale (m L : ℕ) (hL : 0 < L)
    (P : ℕ → ActualIntervals (m + 1)) (r : ℕ) :
    actualReducedRows m L P (L * r) = reducedGaussianRow (P r) := by
  funext h
  simp only [actualReducedRows, Nat.mul_div_cancel_left r hL]

theorem actual_reduced_auxiliaryFamily (m L : ℕ) (hL : 0 < L)
    (A : Fin (m + 1) → ℕ) (hA : ∀ a, 2 * A a < L)
    (P : ℕ → ActualIntervals (m + 1))
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (Y : ℝ) (hY : 1 / 2 < Y)
    (γ : ℝ) (hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp ((γ - ε) * ((L * N : ℕ) : ℝ)) ≤ ((P N).actualAuxiliaryPrimeDivisor : ℝ)) :
    AuxiliaryFamily m L (actualDecay m L A Y + γ) (actualGrowth m L A - γ)
      (actualReducedRows m L P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr h
    rw [actualReducedRows_at_scale m L hL P r]
    simpa only [Nat.add_sub_cancel_right] using reducedGaussianRow_degree (P r) h
  · intro r hr
    rw [actualReducedRows_at_scale m L hL P r]
    exact reducedGaussianRow_matrix_det m (P r)
  · intro η hη
    have hR := reduced_remainders_eventually m L hL A hA P hn hl Y hY γ hdiv hη
    have hH := reduced_disk_heights_eventually m L hL A P hn hl γ hdiv hη
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hR.and hH)
    refine ⟨L * N, ?_⟩
    intro r hr hNr
    have hNr' : N ≤ r := by nlinarith
    have hall := hN r hNr'
    rw [actualReducedRows_at_scale m L hL P r]
    exact ⟨hall.1, hall.2.1, hall.2.2⟩

end OddPiPowers
