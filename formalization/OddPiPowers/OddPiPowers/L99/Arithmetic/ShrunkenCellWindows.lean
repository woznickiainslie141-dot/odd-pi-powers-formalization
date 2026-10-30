module

public import OddPiPowers.L99.Arithmetic.PeriodWindowFamily

/-! Strict interior templates with a uniform, finite-period shrink loss. -/

@[expose] public section

namespace OddPiPowers.L99.PrimeRates

open OddPiPowers.PrimeRates

open scoped BigOperators

noncomputable def shrunkenCellWindow (c : TwentyEightCellCertificate)
    (hc : c ∈ twentyEightLayerCellTable) (ε : ℝ) (he : 0 < ε) (he2 : ε < 1 / 2) :
    CertifiedCellWindow where
  cell := c
  mem_table := hc
  period := 0
  a := (c.left : ℝ) + ε * ((c.right : ℝ) - (c.left : ℝ))
  b := (c.right : ℝ) - ε * ((c.right : ℝ) - (c.left : ℝ))
  left_lt := by
    have hw : (c.left : ℝ) < (c.right : ℝ) := by
      exact_mod_cast (TwentyEightCellCertificate.unit_interval_of_valid
        (twentyEightLayerCellTable_all_valid c hc)).2.1
    nlinarith
  a_lt_b := by
    have hw : (c.left : ℝ) < (c.right : ℝ) := by
      exact_mod_cast (TwentyEightCellCertificate.unit_interval_of_valid
        (twentyEightLayerCellTable_all_valid c hc)).2.1
    nlinarith
  right_gt := by
    have hw : (c.left : ℝ) < (c.right : ℝ) := by
      exact_mod_cast (TwentyEightCellCertificate.unit_interval_of_valid
        (twentyEightLayerCellTable_all_valid c hc)).2.1
    nlinarith

theorem shrunkenCellWindow_cap (c : TwentyEightCellCertificate)
    (hc : c ∈ twentyEightLayerCellTable) (ε : ℝ) (he : 0 < ε) (he2 : ε < 1 / 2)
    (hl : (1 / 99 : ℝ) ≤ (c.left : ℝ)) :
    1 ≤ (99 : ℝ) * (shrunkenCellWindow c hc ε he he2).a := by
  have ht := (shrunkenCellWindow c hc ε he he2).left_lt
  change (c.left : ℝ) < (shrunkenCellWindow c hc ε he he2).a at ht
  nlinarith

theorem reciprocal_shift_loss {x d ε : ℝ} (hx : 1 / 99 ≤ x)
    (hd : 0 ≤ d) (hde : d ≤ ε) :
    1 / x - 1 / (x + d) ≤ (99 : ℝ) ^ 2 * ε := by
  have hx0 : 0 < x := by linarith
  have hxd : 0 < x + d := by linarith
  have he : 0 ≤ ε := hd.trans hde
  have hden : (1 : ℝ) / 99 ^ 2 ≤ x * (x + d) := by nlinarith
  have hid : 1 / x - 1 / (x + d) = d / (x * (x + d)) := by
    field_simp
    ring
  rw [hid]
  apply (div_le_iff₀ (mul_pos hx0 hxd)).mpr
  nlinarith

theorem periodGap_shrink_loss (r : ℕ) {l u ε : ℝ}
    (hl : 1 / 99 ≤ l) (hu : u ≤ 1) (hlu : l < u)
    (he : 0 < ε) (he2 : ε < 1 / 2) :
    periodGap r l u - periodGap r (l + ε * (u - l)) (u - ε * (u - l)) ≤
      2 * (99 : ℝ) ^ 2 * ε := by
  have hd : 0 ≤ ε * (u - l) := by positivity
  have hde : ε * (u - l) ≤ ε := by nlinarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ha : 1 / 99 ≤ (r : ℝ) + l := by linarith
  have hb : 1 / 99 ≤ (r : ℝ) + (u - ε * (u - l)) := by nlinarith
  have h1 := reciprocal_shift_loss ha hd hde
  have h2 := reciprocal_shift_loss hb hd hde
  have heq : (r : ℝ) + (u - ε * (u - l)) + ε * (u - l) = (r : ℝ) + u := by ring
  rw [heq] at h2
  rw [add_assoc] at h1
  unfold periodGap
  linarith

end OddPiPowers.L99.PrimeRates
