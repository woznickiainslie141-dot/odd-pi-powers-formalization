module

public import OddPiPowers.Transfer.IrrationalityTransfer
public import Mathlib.Tactic.Ring

/-! P6 certificate soundness: one-sided rate rounding and positive-gap arithmetic.
The actual AuxiliaryFamily remains an explicit hypothesis. -/

@[expose] public section

namespace OddPiPowers

theorem rate_gap_pos_of_bounds (k : ℕ) (D G d g : ℝ)
    (hD : d ≤ D) (hG : G ≤ g) (hgap : 0 < d - ((k - 1 : ℕ) : ℝ) * g) :
    0 < D - ((k - 1 : ℕ) : ℝ) * G := by
  have ht := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ _)
  linarith

theorem rate_ratio_le_of_bounds (m k : ℕ) (D G d g : ℝ)
    (hD : d ≤ D) (hG0 : 0 ≤ G) (hG : G ≤ g)
    (hgap : 0 < d - ((k - 1 : ℕ) : ℝ) * g) :
    (m : ℝ) * (D + G) / (D - ((k - 1 : ℕ) : ℝ) * G) ≤
      (m : ℝ) * (d + g) / (d - ((k - 1 : ℕ) : ℝ) * g) := by
  have ht : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hg0 : 0 ≤ g := hG0.trans hG
  have hd0 : 0 ≤ d := by nlinarith [mul_nonneg ht hg0]
  have hD0 : 0 ≤ D := hd0.trans hD
  have hc : d * G ≤ D * g := mul_le_mul hD hG hG0 hD0
  have hc' : 0 ≤ D * g - d * G := sub_nonneg.mpr hc
  have hgap' := rate_gap_pos_of_bounds k D G d g hD hG hgap
  apply (div_le_div_iff₀ hgap' hgap).mpr
  have he : (m : ℝ) * (d + g) * (D - ((k - 1 : ℕ) : ℝ) * G) -
      (m : ℝ) * (D + G) * (d - ((k - 1 : ℕ) : ℝ) * g) =
        (m : ℝ) * (((k - 1 : ℕ) : ℝ) + 1) * (D * g - d * G) := by ring
  apply sub_nonneg.mp
  rw [he]
  positivity

theorem rational_rate_certificate_sound (m k : ℕ) (d g target : ℚ)
    (hgap : 0 < d - ((k - 1 : ℕ) : ℚ) * g)
    (hcross : (m : ℚ) * (d + g) < target * (d - ((k - 1 : ℕ) : ℚ) * g))
    (D G : ℝ) (hD : (d : ℝ) ≤ D) (hG0 : 0 ≤ G) (hG : G ≤ (g : ℝ)) :
    (m : ℝ) * (D + G) / (D - ((k - 1 : ℕ) : ℝ) * G) < (target : ℝ) := by
  have hgapR : 0 < (d : ℝ) - ((k - 1 : ℕ) : ℝ) * (g : ℝ) := by exact_mod_cast hgap
  apply (rate_ratio_le_of_bounds m k D G d g hD hG0 hG hgapR).trans_lt
  apply (div_lt_iff₀ hgapR).mpr
  exact_mod_cast hcross

theorem irrationality_transfer_of_rational_certificate (m L k : ℕ) (D G : ℝ)
    (hm : 1 ≤ m) (hL : 0 < L) (hk : 2 ≤ k) (hG0 : 0 ≤ G)
    (d g target : ℚ) (hD : (d : ℝ) ≤ D) (hG : G ≤ (g : ℝ))
    (hgap : 0 < d - ((k - 1 : ℕ) : ℚ) * g)
    (hcross : (m : ℚ) * (d + g) < target * (d - ((k - 1 : ℕ) : ℚ) * g))
    (U : ℕ → Fin (m + 1) → Polynomial GaussianInt)
    (hfamily : AuxiliaryFamily m L D G U) :
    ∃ B : ℝ, B < (target : ℝ) ∧ ExponentUpperBound (Real.pi ^ k) B := by
  have hgapR : 0 < (d : ℝ) - ((k - 1 : ℕ) : ℝ) * (g : ℝ) := by exact_mod_cast hgap
  exact ⟨_, rational_rate_certificate_sound m k d g target hgap hcross D G hD hG0 hG,
    irrationality_transfer m L k D G hm hL hk hG0
      (rate_gap_pos_of_bounds k D G d g hD hG hgapR) U hfamily⟩

end OddPiPowers
