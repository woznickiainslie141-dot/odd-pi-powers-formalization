module

public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.Linarith

/-! An eventual lower-bound interface for irrationality exponents. -/

@[expose] public section

namespace OddPiPowers

open Filter
open scoped Topology

/-- All numerators and all sufficiently large positive denominators are
included. The constant may depend on the exponent slack. -/
def ExponentUpperBound (ξ E : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ Q : ℕ,
    ∀ (p : ℤ) (q : ℕ), 0 < q → Q ≤ q →
      c * (q : ℝ) ^ (-(E + ε)) ≤ |ξ - (p : ℝ) / q|

/-- Taking all fractions, not just reduced fractions, also proves that the
target is irrational: arbitrarily large multiples represent each rational. -/
theorem irrational_of_exponentUpperBound {ξ E : ℝ} (h : ExponentUpperBound ξ E) :
    Irrational ξ := by
  by_contra hξ
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hξ
  obtain ⟨c, hc, Q, hQ⟩ := h 1 zero_lt_one
  let q : ℕ := r.den * (Q + 1)
  let p : ℤ := r.num * (Q + 1 : ℕ)
  have hq : 0 < q := Nat.mul_pos r.den_pos (Nat.succ_pos Q)
  have hqQ : Q ≤ q := (Nat.le_succ Q).trans (Nat.le_mul_of_pos_left (Q + 1) r.den_pos)
  have hrepr : (r : ℝ) = (p : ℝ) / q := by
    dsimp [p, q]
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hpositive : 0 < c * (q : ℝ) ^ (-(E + 1)) :=
    mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hq) _)
  have hlower := hQ p q hq hqQ
  have hz : ξ - (p : ℝ) / q = 0 := by rw [hr, hrepr, sub_self]
  rw [hz, abs_zero] at hlower
  exact (not_le_of_gt hpositive) hlower

/-- Every exponent strictly larger than the bound fails Mathlib's standard
infinitely-often approximation predicate, even allowing an arbitrary constant. -/
theorem not_liouvilleWith_of_exponentUpperBound {ξ E u : ℝ}
    (h : ExponentUpperBound ξ E) (hu : E < u) : ¬ LiouvilleWith u ξ := by
  intro hL
  let δ : ℝ := (u - E) / 4
  let v : ℝ := E + 2 * δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hvu : v < u := by dsimp [v, δ]; linarith
  obtain ⟨c, hc, Q, hQ⟩ := h δ hδ
  have hgrowth : ∀ᶠ q : ℕ in atTop, c⁻¹ < (q : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop c⁻¹)
  have hevent : ∀ᶠ q : ℕ in atTop, 1 ≤ q ∧ Q ≤ q ∧ c⁻¹ < (q : ℝ) ^ δ := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop Q, hgrowth] with q hq hqQ hg
    exact ⟨hq, hqQ, hg⟩
  obtain ⟨q, ⟨p, _, hsmall⟩, hq, hqQ, hg⟩ :=
    ((hL.frequently_lt_rpow_neg hvu).and_eventually hevent).exists
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hmul : (1 : ℝ) < c * (q : ℝ) ^ δ := by
    have ht := mul_lt_mul_of_pos_left hg hc
    simpa only [mul_inv_cancel₀ hc.ne'] using ht
  have hpoweq : (q : ℝ) ^ δ * (q : ℝ) ^ (-v) = (q : ℝ) ^ (-(E + δ)) := by
    rw [← Real.rpow_add hqpos]
    congr 1
    dsimp [v]
    ring
  have hstrict : (q : ℝ) ^ (-v) < c * (q : ℝ) ^ (-(E + δ)) := by
    calc
      _ = 1 * (q : ℝ) ^ (-v) := by simp
      _ < (c * (q : ℝ) ^ δ) * (q : ℝ) ^ (-v) :=
        mul_lt_mul_of_pos_right hmul (Real.rpow_pos_of_pos hqpos _)
      _ = _ := by rw [mul_assoc, hpoweq]
  have hlower := hQ p q (Nat.lt_of_lt_of_le Nat.zero_lt_one hq) hqQ
  linarith

/-- Conversely, absence of infinitely many approximations above `E` gives the
eventual lower bound. Irrationality rules out the excluded equality case. -/
theorem exponentUpperBound_of_not_liouvilleWith {ξ E : ℝ} (hξ : Irrational ξ)
    (h : ∀ u : ℝ, E < u → ¬ LiouvilleWith u ξ) : ExponentUpperBound ξ E := by
  intro ε hε
  have hnot : ¬ ∃ᶠ q : ℕ in atTop, ∃ p : ℤ,
      ξ ≠ (p : ℝ) / q ∧ |ξ - (p : ℝ) / q| < 1 / (q : ℝ) ^ (E + ε) := by
    intro hf
    exact h (E + ε) (by linarith) ⟨1, hf⟩
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (not_frequently.mp hnot)
  refine ⟨1, zero_lt_one, Q, ?_⟩
  intro p q hq hqQ
  have hp : ξ ≠ (p : ℝ) / q := by
    simpa only [Int.cast_natCast] using hξ.ne_rational p (q : ℤ)
  have hnotlt : ¬ |ξ - (p : ℝ) / q| < 1 / (q : ℝ) ^ (E + ε) := by
    intro hlt
    exact hQ q hqQ ⟨p, hp, hlt⟩
  have hlower := le_of_not_gt hnotlt
  simpa only [one_mul, Real.rpow_neg (Nat.cast_nonneg q), one_div] using hlower

theorem exponentUpperBound_iff {ξ E : ℝ} : ExponentUpperBound ξ E ↔
    Irrational ξ ∧ ∀ u : ℝ, E < u → ¬ LiouvilleWith u ξ := by
  constructor
  · intro h
    exact ⟨irrational_of_exponentUpperBound h,
      fun _ hu => not_liouvilleWith_of_exponentUpperBound h hu⟩
  · rintro ⟨hξ, h⟩
    exact exponentUpperBound_of_not_liouvilleWith hξ h

end OddPiPowers
