/-
Adapted from PrimeNumberTheoremAnd, Apache-2.0.
Pinned upstream commit: 127b50e33f6033e2147921167a117af96d9ba4ea.
Original file: PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
See PROVENANCE.json and LICENSE in this directory.
-/

module

public import Mathlib.Algebra.Notation.Support

@[expose] public section

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
