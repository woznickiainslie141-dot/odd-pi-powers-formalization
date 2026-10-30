module

public import OddPiPowers.Arithmetic.TwelveLayerCells
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Pairwise

@[expose] public section

namespace OddPiPowers

def twelveCellsNext (a b : TwelveCellCertificate) : Prop :=
  a.rightNumerator = b.leftNumerator ∧ a.rightDenominator = b.leftDenominator

instance (a b : TwelveCellCertificate) : Decidable (twelveCellsNext a b) := by
  unfold twelveCellsNext
  infer_instance

-- This checks endpoint equality only, not the expensive cost calculations.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem twelveLayerCellTable_next : twelveLayerCellTable.IsChain twelveCellsNext := by
  decide

theorem twelveLayerCellTable_touching :
    twelveLayerCellTable.IsChain (fun a b => a.right = b.left) := by
  refine List.IsChain.imp_of_mem_imp ?_ twelveLayerCellTable_next
  intro a b _ _ h
  rcases h with ⟨hn, hd⟩
  simp only [TwelveCellCertificate.right, TwelveCellCertificate.left, hn, hd]

private theorem twelvePairwise_of_touching (cs : List TwelveCellCertificate) :
    (∀ c ∈ cs, c.left < c.right) →
    cs.IsChain (fun a b => a.right = b.left) →
    cs.Pairwise (fun a b => a.right ≤ b.left) := by
  induction cs with
  | nil => intro _ _; simp
  | cons a cs ih =>
    intro hv hc
    cases cs with
    | nil => simp
    | cons b rest =>
      have hlink := (List.isChain_cons_cons.mp hc).1
      have hchain := (List.isChain_cons_cons.mp hc).2
      have htail := ih (fun c h => hv c (List.mem_cons_of_mem a h)) hchain
      apply List.pairwise_cons.mpr
      refine ⟨?_, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with hxb | hrest
      · subst x
        exact hlink.le
      · calc
          a.right = b.left := hlink
          _ ≤ b.right := (hv b (by simp)).le
          _ ≤ x.left := (List.pairwise_cons.mp htail).1 x hrest

theorem twelveLayerCellTable_pairwise_disjoint :
    twelveLayerCellTable.Pairwise (fun a b => a.right ≤ b.left) :=
  twelvePairwise_of_touching twelveLayerCellTable
    (fun c hc => (TwelveCellCertificate.unit_interval_of_valid
      (twelveLayerCellTable_all_valid c hc)).2.1)
    twelveLayerCellTable_touching

theorem twelveLayerCellTable_compare {a b : TwelveCellCertificate}
    (ha : a ∈ twelveLayerCellTable) (hb : b ∈ twelveLayerCellTable) :
    a = b ∨ a.right ≤ b.left ∨ b.right ≤ a.left := by
  rcases List.mem_iff_get.mp ha with ⟨i, hi⟩
  rcases List.mem_iff_get.mp hb with ⟨j, hj⟩
  rcases lt_trichotomy i.val j.val with h | h | h
  · right; left
    have hij : i < j := h
    simpa only [hi, hj] using twelveLayerCellTable_pairwise_disjoint.rel_get_of_lt hij
  · left
    have hij : i = j := Fin.ext h
    rw [← hi, ← hj, hij]
  · right; right
    have hji : j < i := h
    simpa only [hi, hj] using twelveLayerCellTable_pairwise_disjoint.rel_get_of_lt hji

end OddPiPowers

end
