module

public import OddPiPowers.Arithmetic.PrimeWindowGeometry
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open scoped BigOperators

namespace OddPiPowers.PrimeRates

/-- Total weight of the windows which contain the point `z`. -/
noncomputable def windowWeightSum {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (z : ℝ) : ℕ := by
  classical
  exact ∑ i ∈ s,
    if (W i).lower ≤ z ∧ z < (W i).upper then (W i).weight else 0

/-- Pairwise separated windows cannot both contain the same point. -/
theorem active_window_indices_eq {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow)
    (hdisj : (s : Set ι).Pairwise (fun i j : ι =>
      (W i).upper ≤ (W j).lower ∨ (W j).upper ≤ (W i).lower))
    {i j : ι} (z : ℝ) (hi : i ∈ s) (hj : j ∈ s)
    (hactivei : (W i).lower ≤ z) (hiupper : z < (W i).upper)
    (hactivej : (W j).lower ≤ z) (hjupper : z < (W j).upper) : i = j := by
  classical
  by_contra hne
  have hsep := hdisj hi hj hne
  rcases hsep with hsep | hsep
  · exact (not_lt_of_ge (hsep.trans hactivej)) hiupper
  · exact (not_lt_of_ge (hsep.trans hactivei)) hjupper

/-- A separated finite window family contributes at most its pointwise bound.
The disjointness hypothesis makes the active support empty or a singleton. -/
theorem windowWeightSum_le_of_pairwise {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (B : ℝ → ℕ) (z : ℝ)
    (hdisj : (s : Set ι).Pairwise (fun i j : ι =>
      (W i).upper ≤ (W j).lower ∨ (W j).upper ≤ (W i).lower))
    (hlocal : ∀ i ∈ s, ∀ z : ℝ,
      (W i).lower ≤ z → z < (W i).upper → (W i).weight ≤ B z) :
    windowWeightSum s W z ≤ B z := by
  classical
  by_cases hex : ∃ i, i ∈ s ∧
      (W i).lower ≤ z ∧ z < (W i).upper
  · obtain ⟨i, hi, hactive⟩ := hex
    have hsum : windowWeightSum s W z = (W i).weight := by
      unfold windowWeightSum
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [hactive]
      · intro j hj hji
        by_cases hactivej : (W j).lower ≤ z ∧ z < (W j).upper
        · have hsame := active_window_indices_eq s W hdisj z hi hj
            hactive.1 hactive.2 hactivej.1 hactivej.2
          exact False.elim (hji hsame.symm)
        · simp [hactivej]
    rw [hsum]
    exact hlocal i hi z hactive.1 hactive.2
  · have hzero : windowWeightSum s W z = 0 := by
      unfold windowWeightSum
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hactive : (W i).lower ≤ z ∧ z < (W i).upper
      · exact False.elim (hex ⟨i, hi, hactive⟩)
      · simp [hactive]
    rw [hzero]
    exact Nat.zero_le _

end OddPiPowers.PrimeRates

end
