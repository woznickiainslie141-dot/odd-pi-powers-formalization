import OddPiPowers.Arithmetic.TwelveLayerCells
open OddPiPowers
private theorem monotone_fin24 {α : Type} [Preorder α] (f : Fin 24 → α)
    (hstep : ∀ k : Fin 23, f k.castSucc ≤ f k.succ) :
    ∀ a b : Fin 24, a.val ≤ b.val → f a ≤ f b := by
  intro a b hab
  let d := b.val - a.val
  have hd : b.val = a.val + d := by simp [d]; omega
  have aux : ∀ d (b : Fin 24), b.val = a.val + d → f a ≤ f b := by
    intro n
    induction n with
    | zero =>
      intro b hb
      have hEq : b = a := Fin.ext (by simpa using hb)
      subst b
      exact le_rfl
    | succ n ih =>
      intro b hb
      let mid : Fin 24 := ⟨a.val + n, by omega⟩
      have hmid : mid.val = a.val + n := by simp [mid]
      have hfirst := ih mid hmid
      have hlt : mid.val < 23 := by simp [mid]; omega
      let k : Fin 23 := ⟨mid.val, hlt⟩
      have hadj := hstep k
      have hleft : k.castSucc = mid := by apply Fin.ext; rfl
      have hright : k.succ = b := by apply Fin.ext; simp [k]; omega
      rw [hleft, hright] at hadj
      exact hfirst.trans hadj
  exact aux d b hd
#check monotone_fin24
