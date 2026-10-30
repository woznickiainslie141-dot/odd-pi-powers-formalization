module

public import OddPiPowers.Arithmetic.PrimeWindowGeometry
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Positivity

@[expose] public section

open scoped BigOperators
open Real Finset

namespace OddPiPowers.PrimeRates

theorem PrimeWindow.eventually_large (W : PrimeWindow) (L : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, (L : ℝ) * W.upper ^ 2 < (N : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (Filter.eventually_gt_atTop _)

/-- Primes in the half-open reciprocal interval belonging to `W`. -/
noncomputable def PrimeWindow.primes (W : PrimeWindow) (N : ℕ) : Finset ℕ :=
  Nat.primesLE ⌊(N : ℝ) / W.lower⌋₊ \ Nat.primesLE ⌊(N : ℝ) / W.upper⌋₊

theorem PrimeWindow.mem_primes (W : PrimeWindow) (N p : ℕ) :
    p ∈ W.primes N ↔ p.Prime ∧
      (N : ℝ) / W.upper < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) / W.lower := by
  have hlow : 0 ≤ (N : ℝ) / W.lower := div_nonneg (Nat.cast_nonneg N) W.lower_pos.le
  have hupp : 0 ≤ (N : ℝ) / W.upper := div_nonneg (Nat.cast_nonneg N) W.upper_pos.le
  simp only [PrimeWindow.primes, mem_sdiff, Nat.mem_primesLE, Nat.le_floor_iff hlow,
    Nat.le_floor_iff hupp]
  constructor
  · rintro ⟨⟨h₁, hp⟩, h₂⟩
    exact ⟨hp, lt_of_not_ge (fun h => h₂ ⟨h, hp⟩), h₁⟩
  · rintro ⟨hp, h₁, h₂⟩
    exact ⟨⟨h₂, hp⟩, fun h => h₁.not_ge h.1⟩

theorem PrimeWindow.mem_primes_quotient (W : PrimeWindow) (N p : ℕ) (hp : p.Prime) :
    p ∈ W.primes N ↔ W.lower ≤ (N : ℝ) / (p : ℝ) ∧
      (N : ℝ) / (p : ℝ) < W.upper := by
  rw [W.mem_primes, and_iff_right hp]
  exact W.reciprocal_mem_iff (by exact_mod_cast hp.pos)

theorem PrimeWindow.sum_log_primes (W : PrimeWindow) (N : ℕ) :
    (∑ p ∈ W.primes N, log (p : ℝ)) =
      Chebyshev.theta ((N : ℝ) / W.lower) -
        Chebyshev.theta ((N : ℝ) / W.upper) := by
  have hsub : Nat.primesLE ⌊(N : ℝ) / W.upper⌋₊ ⊆
      Nat.primesLE ⌊(N : ℝ) / W.lower⌋₊ := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (Nat.floor_le_floor
      (div_le_div_of_nonneg_left (Nat.cast_nonneg N) W.lower_pos W.lower_lt_upper.le)), hp.2⟩
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  exact Finset.sum_sdiff_eq_sub hsub

end OddPiPowers.PrimeRates

end
