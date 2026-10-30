module

public import OddPiPowers.Transfer.OneScale

/-! Quantitative transfer with a fixed positive rate slack. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

/-- The close, positive-rational case. The constant is chosen before the
numerator and denominator, and no reducedness condition is used. -/
theorem fixed_slack_close_bound (m L k : ℕ) (D G η : ℝ)
    (hL : 0 < L) (hk : 0 < k) (hG : 0 ≤ G) (hη : 0 < η)
    (hgap : 0 < D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η)
    (U : ℕ → Fin (m + 1) → GaussianInt[X]) (hfamily : AuxiliaryFamily m L D G U) :
    let β := D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η
    let E := (m : ℝ) + (k : ℝ) * (G + η) * m / β
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q → 0 < (p : ℝ) / q →
      |Real.pi ^ k - (p : ℝ) / q| < ((4 : ℝ) ^ k - Real.pi ^ k) / 2 →
      c * (q : ℝ) ^ (-E) ≤ |Real.pi ^ k - (p : ℝ) / q| := by
  dsimp only
  let β : ℝ := D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η
  let t : ℝ := G + η
  let E : ℝ := (m : ℝ) + (k : ℝ) * t * m / β
  obtain ⟨N, hN⟩ := auxiliary_distance_at_scale m L k D G U hfamily hG hk η hη
  let C₀ : ℝ := (L : ℝ) * (N + 2)
  let C₁ : ℝ := Real.exp (-((k : ℝ) * t) * (Real.log 2 / β + C₀)) / 2
  let P : ℝ := 2 * Real.pi ^ (k - 1)
  let c : ℝ := P * C₁ * ((2 : ℝ) ^ k) ^ (-E)
  have hβ : 0 < β := hgap
  have ht : 0 ≤ t := add_nonneg hG hη.le
  have hP : 0 < P := by dsimp [P]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (mul_pos hP hC₁) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨c, hc, ?_⟩
  intro p q hq hp hclose
  obtain ⟨θ, hθpos, hθ⟩ := exists_positive_nth_root ((p : ℝ) / q) hp k hk
  have hyDisk : ‖Complex.I * (θ : ℂ) / 2‖ ≤ 2 := by
    apply root_in_disk_of_close k hk θ hθpos.le
    simpa only [hθ] using hclose
  let B : ℝ := (2 : ℝ) ^ k * q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hB : 0 < B := zero_lt_one.trans_le hB1
  let s : ℝ := (m : ℝ) * Real.log B + Real.log 2
  let x : ℝ := s / ((L : ℝ) * β)
  let r : ℕ := max (N + 1) ⌈x⌉₊
  have hr : 0 < r := lt_of_lt_of_le (Nat.succ_pos N) (le_max_left _ _)
  have hnN : N ≤ L * r := roundedIndex_threshold L N x hL
  have hbounds := rounded_rate_bounds L N m β B hL hβ hB1
  have hlower : s ≤ β * (L * r : ℕ) := by
    simpa only [s, x, r, roundedIndex] using hbounds.1
  have hupper : (L * r : ℕ) ≤ s / β + C₀ := by
    simpa only [s, x, r, C₀, roundedIndex] using hbounds.2
  have hkcast : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_of_lt hk))
  have hbetaeq : β + ((k - 1 : ℕ) : ℝ) * t = D - η := by
    dsimp [β, t]
    rw [← hkcast]
    ring
  have hscale : (m : ℝ) * Real.log B + ((k - 1 : ℕ) : ℝ) *
      (t * (L * r : ℕ)) + Real.log 2 ≤ (D - η) * (L * r : ℕ) := by
    calc
      _ = s + (((k - 1 : ℕ) : ℝ) * t) * (L * r : ℕ) := by dsimp [s]; ring
      _ ≤ β * (L * r : ℕ) + (((k - 1 : ℕ) : ℝ) * t) * (L * r : ℕ) := by
        linarith
      _ = _ := by rw [← add_mul, hbetaeq]
  have hdist := hN r hr hnN p q hq θ hθ hyDisk (by simpa only [B, t] using hscale)
  have hdist' : Real.exp (-((m : ℝ) * Real.log B + (k : ℝ) * (t * (L * r : ℕ)))) / 2 ≤
      ‖lambda - Complex.I * (θ : ℂ) / 2‖ := by
    rw [← one_scale_factor_eq B (t * (L * r : ℕ)) hB m k hk]
    simpa only [B, t] using hdist
  have hexp := exp_lower_of_index_upper B β t (L * r : ℕ) C₀ m k hB hβ ht hupper
  have hrootdist : C₁ * B ^ (-E) ≤ ‖lambda - Complex.I * (θ : ℂ) / 2‖ := by
    apply le_trans _ hdist'
    simpa only [C₁, E, s, mul_assoc] using hexp
  have hpower := pi_power_distance_lower k hk θ hθpos.le
  have hmul := mul_le_mul_of_nonneg_left hrootdist hP.le
  calc
    c * (q : ℝ) ^ (-E) = P * (C₁ * B ^ (-E)) := by
      rw [show B = (2 : ℝ) ^ k * q from rfl,
        Real.mul_rpow (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)]
      dsimp [c]
      ring
    _ ≤ P * ‖lambda - Complex.I * (θ : ℂ) / 2‖ := hmul
    _ ≤ |Real.pi ^ k - (p : ℝ) / q| := by
      simpa only [P, hθ] using hpower

/-- The fixed-slack estimate for every numerator and positive denominator. -/
theorem fixed_slack_bound (m L k : ℕ) (D G η : ℝ)
    (hL : 0 < L) (hk : 0 < k) (hG : 0 ≤ G) (hη : 0 < η)
    (hgap : 0 < D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η)
    (U : ℕ → Fin (m + 1) → GaussianInt[X]) (hfamily : AuxiliaryFamily m L D G U) :
    let β := D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η
    let E := (m : ℝ) + (k : ℝ) * (G + η) * m / β
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
      c * (q : ℝ) ^ (-E) ≤ |Real.pi ^ k - (p : ℝ) / q| := by
  dsimp only
  let β : ℝ := D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η
  let E : ℝ := (m : ℝ) + (k : ℝ) * (G + η) * m / β
  let δ : ℝ := ((4 : ℝ) ^ k - Real.pi ^ k) / 2
  obtain ⟨c₀, hc₀, hclose⟩ := fixed_slack_close_bound m L k D G η hL hk hG hη hgap U hfamily
  let c : ℝ := min c₀ (min δ (Real.pi ^ k))
  have hδ : 0 < δ := pi_power_cutoff_pos k hk
  have hπ : 0 < Real.pi ^ k := pow_pos Real.pi_pos _
  have hc : 0 < c := lt_min hc₀ (lt_min hδ hπ)
  have hE : 0 ≤ E := by
    dsimp [E]
    apply add_nonneg (Nat.cast_nonneg _)
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hG hη.le))
      (Nat.cast_nonneg _)) hgap.le
  refine ⟨c, hc, ?_⟩
  intro p q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow0 : 0 ≤ (q : ℝ) ^ (-E) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hpow1 : (q : ℝ) ^ (-E) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (neg_nonpos.mpr hE)
  have hcsmall : c * (q : ℝ) ^ (-E) ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow1 hc.le
  by_cases hp : 0 < (p : ℝ) / q
  · by_cases hd : |Real.pi ^ k - (p : ℝ) / q| < δ
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hpow0).trans
        (hclose p q hq hp hd)
    · exact hcsmall.trans ((min_le_right _ _).trans
        ((min_le_left _ _).trans (le_of_not_gt hd)))
  · have herror : Real.pi ^ k ≤ |Real.pi ^ k - (p : ℝ) / q| := by
      have hp' : (p : ℝ) / q ≤ 0 := le_of_not_gt hp
      exact (show Real.pi ^ k ≤ Real.pi ^ k - (p : ℝ) / q by linarith).trans
        (le_abs_self _)
    exact hcsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans herror))

end OddPiPowers
