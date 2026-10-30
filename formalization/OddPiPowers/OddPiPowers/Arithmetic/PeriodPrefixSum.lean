module

public import OddPiPowers.Arithmetic.PeriodFloorBlock
public import OddPiPowers.Arithmetic.CellWindowAggregate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-! Draft bridge between list-based prefix certificates and cell rates.
This file has not been compiled by the helper. -/

@[expose] public section

open scoped BigOperators

namespace OddPiPowers.PrimeRates

theorem periodPrefixLabels_append (T : ℕ) (cs₁ cs₂ : List TwelveCellCertificate) :
    periodPrefixLabels T (cs₁ ++ cs₂) =
      periodPrefixLabels T cs₁ ++ periodPrefixLabels T cs₂ := by
  simp [periodPrefixLabels]

theorem periodPrefixLabels_actual_sum_append (T : ℕ)
    (cs₁ cs₂ : List TwelveCellCertificate) :
    ((periodPrefixLabels T (cs₁ ++ cs₂)).map periodLabelActual).sum =
      ((periodPrefixLabels T cs₁).map periodLabelActual).sum +
      ((periodPrefixLabels T cs₂).map periodLabelActual).sum := by
  simp [periodPrefixLabels_append]

/-- This identity holds even for repeated cells: the list sum counts each
occurrence. The later finset bridge explicitly assumes `Nodup`. -/
theorem periodPrefixLabels_actual_sum_list (T : ℕ) (cs : List TwelveCellCertificate) :
    ((periodPrefixLabels T cs).map periodLabelActual).sum =
      (cs.map (fun c => ∑ r ∈ Finset.range T, periodLabelActual (c, r))).sum := by
  induction cs with
  | nil => simp [periodPrefixLabels]
  | cons c cs ih =>
    have h := List.sum_toFinset (fun r : ℕ => periodLabelActual (c, r))
      (show (List.range T).Nodup from List.nodup_range)
    simp only [List.toFinset_range] at h
    unfold periodPrefixLabels at ih
    simp only [periodPrefixLabels, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    rw [← h, ih]

theorem periodPrefixLabels_actual_sum_finset (T : ℕ) (cs : List TwelveCellCertificate)
    (hnodup : cs.Nodup) :
    ((periodPrefixLabels T cs).map periodLabelActual).sum =
      (1 / 69 : ℝ) * ∑ r ∈ Finset.range T, ∑ c ∈ cs.toFinset,
        (c.value : ℝ) * periodGap r (c.left : ℝ) (c.right : ℝ) := by
  rw [periodPrefixLabels_actual_sum_list]
  rw [← List.sum_toFinset _ hnodup]
  rw [Finset.sum_comm]
  simp only [periodLabelActual]
  simp_rw [div_eq_mul_inv]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro c hc
  ring

set_option maxRecDepth 10000 in
/-- Removing the membership proof from the selected-cell subtype preserves
the finite sum; no quotient of distinct cell values is used. -/
theorem selectedCellSet_sum_val (f : TwelveCellCertificate → ℝ) :
    (∑ c ∈ selectedCellSet, f c.val) = ∑ c ∈ selectedCells.toFinset, f c := by
  classical
  apply Finset.sum_bij (fun c _ => c.val)
  · intro c hc
    exact List.mem_toFinset.mpr c.property
  · intro a ha b hb heq
    exact Subtype.ext heq
  · intro c hc
    have hcm : c ∈ selectedCells := List.mem_toFinset.mp hc
    refine ⟨⟨c, hcm⟩, ?_, rfl⟩
    simp only [selectedCellSet, List.mem_toFinset, List.mem_attach]
  · intro c hc
    rfl

theorem selected_periodPrefixLabels_actual_sum (T : ℕ) :
    ((periodPrefixLabels T selectedCells).map periodLabelActual).sum =
      selectedUnshrunkRate T := by
  rw [periodPrefixLabels_actual_sum_finset T selectedCells selectedCells_nodup]
  unfold selectedUnshrunkRate
  apply congrArg (fun x : ℝ => (1 / 69 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro r hr
  symm
  exact selectedCellSet_sum_val (fun c =>
    (c.value : ℝ) * periodGap r (c.left : ℝ) (c.right : ℝ))

end OddPiPowers.PrimeRates
