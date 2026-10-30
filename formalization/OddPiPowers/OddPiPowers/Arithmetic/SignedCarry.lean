module

public import OddPiPowers.Construction.ActualAuxiliary

@[expose] public section

namespace OddPiPowers

open scoped BigOperators

/-- The carry created by adding two signed integers before taking quotient by
a positive divisor. Integer division here is Euclidean division, so negative
arguments have the required floor convention. -/
def signedCarry (p x y : ℤ) : ℤ := (x + y) / p - x / p - y / p

theorem signedCarry_eq_zero_or_one {p x y : ℤ} (hp : 0 < p) :
    signedCarry p x y = 0 ∨ signedCarry p x y = 1 := by
  by_cases h : p ≤ x % p + y % p
  · rw [signedCarry, Int.add_ediv_of_pos hp, if_pos h]
    right
    ring
  · have h' : ¬ p ≤ x % p + y % p := h
    rw [signedCarry, Int.add_ediv_of_pos hp, if_neg h']
    left
    ring

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

/-- The signed carry attached to one interval and one local index. The two
numerators in the last terms remain integers; in particular, indices outside
the interval use signed rather than truncated division. -/
def intervalCarry (a : Fin M) (p ell : ℕ) : ℤ :=
  (P.length a : ℤ) / (p : ℤ) -
    ((ell : ℤ) - (P.left a : ℤ)) / (p : ℤ) -
    ((P.right a : ℤ) - (ell : ℤ)) / (p : ℤ)

theorem intervalCarry_zero_or_one (a : Fin M) {p ell : ℕ}
    (hp : 0 < p) (hell : ell ≤ P.n) :
    P.intervalCarry a p ell = 0 ∨ P.intervalCarry a p ell = 1 := by
  have hlength : (P.length a : ℤ) = (P.right a : ℤ) - (P.left a : ℤ) := by
    rw [← Int.natCast_sub (P.left_le_right a), ← P.length_eq a]
  have hsum :
      ((ell : ℤ) - (P.left a : ℤ)) +
        ((P.right a : ℤ) - (ell : ℤ)) = (P.length a : ℤ) := by
    rw [hlength]
    ring
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  simpa [intervalCarry, signedCarry, hsum] using
    (signedCarry_eq_zero_or_one (p := (p : ℤ))
      (x := (ell : ℤ) - (P.left a : ℤ))
      (y := (P.right a : ℤ) - (ell : ℤ)) hpZ)

/-- The natural 0/1 version of the signed local carry. -/
def intervalCarryNat (a : Fin M) (p ell : ℕ) : ℕ :=
  (P.intervalCarry a p ell).toNat

theorem intervalCarryNat_eq_zero_or_one (a : Fin M) {p ell : ℕ}
    (hp : 0 < p) (hell : ell ≤ P.n) :
    P.intervalCarryNat a p ell = 0 ∨ P.intervalCarryNat a p ell = 1 := by
  rcases P.intervalCarry_zero_or_one a hp hell with h | h
  · simp [intervalCarryNat, h]
  · simp [intervalCarryNat, h]

/-- The total signed-floor carry weight at a local index. -/
def carryWeight (p ell : ℕ) : ℕ :=
  ∑ a : Fin M, P.intervalCarryNat a p ell

end ActualIntervals

end OddPiPowers

end
