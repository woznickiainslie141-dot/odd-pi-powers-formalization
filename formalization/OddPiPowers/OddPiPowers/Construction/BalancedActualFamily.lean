module

public import OddPiPowers.Construction.ActualAuxiliary

/-! The actual all-pole family; no formal replacement of its coefficients. -/

@[expose] public section

namespace OddPiPowers

def balancedActualFamily (M n : ℕ) : ActualIntervals M where
  n := n
  left := fun _ => 0
  left_mono := fun a b hab => le_rfl
  left_bound := fun a => by simp

theorem balanced_length (M n : ℕ) (a : Fin M) :
    (balancedActualFamily M n).length a = n := by
  simp [ActualIntervals.length, balancedActualFamily]

theorem balanced_interval (M n : ℕ) (a : Fin M) :
    (balancedActualFamily M n).interval a = Finset.range (n + 1) := by
  ext r
  simp [ActualIntervals.interval, ActualIntervals.right, balancedActualFamily]

theorem balanced_multiplicity (M n ell : ℕ) (hell : ell ≤ n) :
    (balancedActualFamily M n).multiplicity ell = M := by
  simp [ActualIntervals.multiplicity, balanced_interval, Finset.mem_range, hell]

noncomputable def balancedBinomialWeight (n ell : ℕ) : ℚ :=
  (((-1 : ℤ) ^ ell * (n.choose ell : ℤ)) : ℚ)

theorem balanced_binomialWeight (M n ell : ℕ) (a : Fin M) :
    (balancedActualFamily M n).binomialWeight a ell = balancedBinomialWeight n ell := by
  simp [ActualIntervals.binomialWeight, balancedActualFamily,
    balancedBinomialWeight, ActualIntervals.length]

theorem balanced_localExpansion (M n ell h : ℕ) (hell : ell ≤ n) :
    (balancedActualFamily M n).localExpansion ell h =
      PowerSeries.C ((balancedBinomialWeight n ell) ^ M) *
        ((PowerSeries.C (-(ell : ℚ)) + PowerSeries.X) ^ h *
          (∏ r ∈ (Finset.range (n + 1)).erase ell,
            normalizedReciprocal ((r : ℤ) - (ell : ℤ))) ^ M) := by
  classical
  have hlocal (a : Fin M) : (balancedActualFamily M n).localFactor a ell =
      PowerSeries.C (balancedBinomialWeight n ell) *
        ∏ r ∈ (Finset.range (n + 1)).erase ell,
          normalizedReciprocal ((r : ℤ) - (ell : ℤ)) := by
    simp only [ActualIntervals.localFactor, balanced_interval, Finset.mem_range,
      Nat.lt_succ_iff, hell, ite_true, ActualIntervals.poleLocalFactor,
      balanced_binomialWeight]
  rw [ActualIntervals.localExpansion]
  simp_rw [hlocal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← map_pow]
  ring

end OddPiPowers
