module

public import OddPiPowers.Transfer.FixedSlack
public import OddPiPowers.Foundations.ExponentUpperBound
public import Mathlib.Topology.Order.LeftRight

/-! The abstract irrationality-measure transfer theorem. -/

@[expose] public section

namespace OddPiPowers

open Filter
open Polynomial
open scoped Topology

/-- Explicit quantifier closure: a positive slack can be chosen so that the
denominator stays positive and the exponent is within any prescribed error. -/
theorem exists_positive_rate_slack (A Δ κ ε : ℝ) (hΔ : 0 < Δ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ 0 < Δ - κ * η ∧ A / (Δ - κ * η) < A / Δ + ε := by
  have hden : ContinuousAt (fun x : ℝ => Δ - κ * x) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hratio : ContinuousAt (fun x : ℝ => A / (Δ - κ * x)) 0 :=
    continuousAt_const.div hden (by simpa using hΔ.ne')
  have hratio' : Tendsto (fun x : ℝ => A / (Δ - κ * x)) (𝓝 0) (𝓝 (A / Δ)) := by
    simpa using hratio.tendsto
  have hden' : Tendsto (fun x : ℝ => Δ - κ * x) (𝓝 0) (𝓝 Δ) := by
    simpa using hden.tendsto
  have hnear : ∀ᶠ x : ℝ in 𝓝 0,
      0 < Δ - κ * x ∧ A / (Δ - κ * x) < A / Δ + ε :=
    (hden'.eventually (eventually_gt_nhds hΔ)).and
      (hratio'.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε)))
  obtain ⟨η, hη, hgap, hbound⟩ := ((frequently_gt_nhds (0 : ℝ)).and_eventually hnear).exists
  exact ⟨η, hη, hgap, hbound⟩

theorem transfer_exponent_identity (m k : ℕ) (D G η : ℝ) (hk : 0 < k)
    (hβ : 0 < D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η) :
    let β := D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η
    (m : ℝ) + (k : ℝ) * (G + η) * m / β = (m : ℝ) * (D + G) / β := by
  dsimp only
  let β : ℝ := D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η
  have hkcast : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_of_lt hk))
  have hsum : β + (k : ℝ) * (G + η) = D + G := by
    dsimp [β]
    rw [← hkcast]
    ring
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  change (m : ℝ) + (k : ℝ) * (G + η) * m / β = (m : ℝ) * (D + G) / β
  calc
    _ = (m : ℝ) * (β + (k : ℝ) * (G + η)) / β := by
      field_simp [hβ0]
    _ = _ := by rw [hsum]

/-- General transfer from a uniformly bounded family of Gaussian-integer
polynomials to an irrationality-exponent upper bound for `π^k`. -/
theorem irrationality_transfer (m L k : ℕ) (D G : ℝ)
    (_hm : 1 ≤ m) (hL : 0 < L) (hk : 2 ≤ k) (hG : 0 ≤ G)
    (hΔ : 0 < D - ((k - 1 : ℕ) : ℝ) * G)
    (U : ℕ → Fin (m + 1) → GaussianInt[X]) (hfamily : AuxiliaryFamily m L D G U) :
    ExponentUpperBound (Real.pi ^ k)
      ((m : ℝ) * (D + G) / (D - ((k - 1 : ℕ) : ℝ) * G)) := by
  intro ε hε
  let Δ : ℝ := D - ((k - 1 : ℕ) : ℝ) * G
  let A : ℝ := (m : ℝ) * (D + G)
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  obtain ⟨η, hη, hβ, hE⟩ := exists_positive_rate_slack A Δ (k : ℝ) ε hΔ hε
  have hβ' : 0 < D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η := hβ
  obtain ⟨c, hc, hbound⟩ := fixed_slack_bound m L k D G η hL hkpos hG hη hβ' U hfamily
  refine ⟨c, hc, 1, ?_⟩
  intro p q hq hqQ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hE' : (m : ℝ) + (k : ℝ) * (G + η) * m /
        (D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η) ≤
      (m : ℝ) * (D + G) / (D - ((k - 1 : ℕ) : ℝ) * G) + ε := by
    rw [transfer_exponent_identity m k D G η hkpos hβ']
    exact hE.le
  have hpow : (q : ℝ) ^ (-((m : ℝ) * (D + G) /
        (D - ((k - 1 : ℕ) : ℝ) * G) + ε)) ≤
      (q : ℝ) ^ (-((m : ℝ) + (k : ℝ) * (G + η) * m /
        (D - ((k - 1 : ℕ) : ℝ) * G - (k : ℝ) * η))) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg hE')
  exact (mul_le_mul_of_nonneg_left hpow hc.le).trans (hbound p q hq)

end OddPiPowers
