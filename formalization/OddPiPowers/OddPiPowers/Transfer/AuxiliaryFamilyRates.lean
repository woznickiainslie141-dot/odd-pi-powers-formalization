module

public import OddPiPowers.Transfer.AuxiliaryFamily
public import Mathlib.Tactic.Linarith

/-! One-sided rate weakening retains all actual family obligations. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

theorem AuxiliaryFamily.weaken_rates {m L : ℕ} {D G d g : ℝ}
    {U : ℕ → Fin (m + 1) → Polynomial GaussianInt}
    (H : AuxiliaryFamily m L D G U) (hd : d ≤ D) (hg : G ≤ g) :
    AuxiliaryFamily m L d g U := by
  refine ⟨H.degree, H.determinant, ?_⟩
  intro η hη
  obtain ⟨N, hN⟩ := H.bounds η hη
  refine ⟨N, ?_⟩
  intro r hr hNr
  obtain ⟨hR, hU, hT⟩ := hN r hr hNr
  have hn : (0 : ℝ) ≤ ((L * r : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (hR i).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith : -(D - η) ≤ -(d - η)) hn))
  · intro i z hz
    exact (hU i z hz).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith : G + η ≤ g + η) hn))
  · intro i z hz
    exact (hT i z hz).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith : G + η ≤ g + η) hn))

end OddPiPowers
