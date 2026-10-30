module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Tactic.GCongr

/-! Bounds for products over roots, retaining their multiplicities. -/

@[expose] public section

namespace OddPiPowers

/-- Isolate one occurrence of a selected root. Repeated roots are retained in
the remaining multiset, so no separability assumption is needed. -/
theorem root_product_bound (s : Multiset ℂ) (y : ℂ) (hy : y ∈ s)
    (g : ℂ → ℂ) (H : NNReal) (hH : 1 ≤ H)
    (hbound : ∀ z ∈ s, ‖g z‖₊ ≤ H) (k : ℕ) (hk : s.card ≤ k) :
    ‖(s.map g).prod‖₊ ≤ ‖g y‖₊ * H ^ (k - 1) := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hy
  have ht : ∀ z ∈ t, ‖g z‖₊ ≤ H := by
    intro z hz
    exact hbound z (by simp [hz])
  have hcard : t.card ≤ k - 1 := by
    simp only [Multiset.card_cons] at hk
    exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hk)
  calc
    ‖((y ::ₘ t).map g).prod‖₊ = ‖g y‖₊ * (t.map fun z => ‖g z‖₊).prod := by
      simp [Multiset.nnnorm_prod_map]
    _ ≤ ‖g y‖₊ * H ^ t.card := by
      gcongr
      simpa using Multiset.prod_le_pow_card (t.map fun z => ‖g z‖₊) H (by
        intro a ha
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
        exact ht z hz)
    _ ≤ ‖g y‖₊ * H ^ (k - 1) := by
      gcongr

/-- Convert the product estimate into a lower bound on the selected value. -/
theorem inverse_product_le_of_one_le_mul (A C x : NNReal) (hA : 0 < A) (hC : 0 < C)
    (h : 1 ≤ A * (x * C)) : 1 / (A * C) ≤ x := by
  apply (div_le_iff₀ (mul_pos hA hC)).2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end OddPiPowers
