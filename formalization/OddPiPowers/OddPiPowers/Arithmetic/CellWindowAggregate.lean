module

public import OddPiPowers.Arithmetic.ShrunkenCellWindows
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.NormNum

/-! Draft aggregation of accepted fine cells into shrunken templates.
This file was not compiled by the helper. -/

@[expose] public section

open scoped BigOperators

namespace OddPiPowers.PrimeRates

def selectedCellPredicate (c : TwelveCellCertificate) : Bool :=
  decide (0 < c.value ∧ c.value ≤ 17 ∧ 0 < c.leftNumerator ∧
    c.leftDenominator ≤ 69 * c.leftNumerator)

def selectedCells : List TwelveCellCertificate :=
  twelveLayerCellTable.filter selectedCellPredicate

theorem selectedCell_mem_table {c : TwelveCellCertificate} (hc : c ∈ selectedCells) :
    c ∈ twelveLayerCellTable := by
  exact (List.mem_filter.mp hc).1

theorem selectedCell_predicate {c : TwelveCellCertificate} (hc : c ∈ selectedCells) :
    0 < c.value ∧ c.value ≤ 17 ∧ 0 < c.leftNumerator ∧
      c.leftDenominator ≤ 69 * c.leftNumerator := by
  have hp := (List.mem_filter.mp hc).2
  exact of_decide_eq_true hp

private theorem nodup_of_ordered_valid (xs : List TwelveCellCertificate)
    (hv : ∀ c ∈ xs, c.left < c.right)
    (ho : xs.Pairwise (fun c d => c.right ≤ d.left)) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    rw [List.nodup_cons]
    constructor
    · intro hc
      have hle : c.right ≤ c.left := (List.pairwise_cons.mp ho).1 c hc
      have hlt := hv c (by simp)
      exact (not_le_of_gt hlt) hle
    · apply ih
      · intro d hd
        exact hv d (by simp [hd])
      · exact (List.pairwise_cons.mp ho).2

theorem twelveLayerCellTable_nodup : twelveLayerCellTable.Nodup := by
  apply nodup_of_ordered_valid
  · intro c hc
    exact (TwelveCellCertificate.unit_interval_of_valid
      (twelveLayerCellTable_all_valid c hc)).2.1
  · exact twelveLayerCellTable_pairwise_disjoint

theorem selectedCells_nodup : selectedCells.Nodup := by
  exact twelveLayerCellTable_nodup.filter selectedCellPredicate

theorem selectedCells_length_le : selectedCells.length ≤ 1180 := by
  have h := List.length_filter_le selectedCellPredicate twelveLayerCellTable
  simpa [selectedCells, twelveLayerCellTable_length] using h

abbrev SelectedCell := { c : TwelveCellCertificate // c ∈ selectedCells }

noncomputable def selectedCellSet : Finset SelectedCell := selectedCells.attach.toFinset

theorem selectedCellSet_card_le : selectedCellSet.card ≤ 1180 := by
  have h := (List.toFinset_card_le (l := selectedCells.attach))
  change selectedCellSet.card ≤ selectedCells.attach.length at h
  exact h.trans (by simpa only [List.length_attach] using selectedCells_length_le)

noncomputable def cellShrinkEpsilon : ℝ := 1 / 10 ^ 24

theorem cellShrinkEpsilon_pos : 0 < cellShrinkEpsilon := by
  norm_num [cellShrinkEpsilon]

theorem cellShrinkEpsilon_lt_half : cellShrinkEpsilon < 1 / 2 := by
  norm_num [cellShrinkEpsilon]

noncomputable def selectedCellTemplate (c : SelectedCell) : CertifiedCellWindow :=
  shrunkenCellWindow c.val (selectedCell_mem_table c.property) cellShrinkEpsilon
    cellShrinkEpsilon_pos cellShrinkEpsilon_lt_half

theorem selectedCellTemplate_cell (c : SelectedCell) :
    (selectedCellTemplate c).cell = c.val := rfl

theorem selectedCellTemplate_cell_inj :
    Set.InjOn (fun c => (selectedCellTemplate c).cell) ↑selectedCellSet := by
  intro a ha b hb heq
  apply Subtype.ext
  simpa only [selectedCellTemplate_cell] using heq

theorem selectedCell_left_lower (c : SelectedCell) : (1 / 69 : ℝ) ≤ (c.val.left : ℝ) := by
  have hc := selectedCell_mem_table c.property
  have hv := twelveLayerCellTable_all_valid c.val hc
  have hden : 0 < c.val.leftDenominator := hv.1
  have hdenR : (0 : ℝ) < c.val.leftDenominator := by exact_mod_cast hden
  have hp := (selectedCell_predicate c.property).2.2.2
  have hpR : (c.val.leftDenominator : ℝ) ≤ 69 * c.val.leftNumerator := by exact_mod_cast hp
  simp only [TwelveCellCertificate.left, Rat.cast_div, Rat.cast_natCast]
  apply (le_div_iff₀ hdenR).2
  linarith

theorem selectedCellTemplate_cap (c : SelectedCell) :
    1 ≤ (69 : ℝ) * (selectedCellTemplate c).a := by
  exact shrunkenCellWindow_cap c.val (selectedCell_mem_table c.property)
    cellShrinkEpsilon cellShrinkEpsilon_pos cellShrinkEpsilon_lt_half (selectedCell_left_lower c)

noncomputable def selectedUnshrunkRate (K : ℕ) : ℝ :=
  (1 / 69 : ℝ) * ∑ r ∈ Finset.range K, ∑ c ∈ selectedCellSet,
    (c.val.value : ℝ) * periodGap r (c.val.left : ℝ) (c.val.right : ℝ)

theorem selectedCell_gap_le (r : ℕ) (c : SelectedCell) :
    (c.val.value : ℝ) * periodGap r (c.val.left : ℝ) (c.val.right : ℝ) ≤
      (c.val.value : ℝ) * periodGap r (selectedCellTemplate c).a (selectedCellTemplate c).b +
        17 * (2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon) := by
  have hc := selectedCell_mem_table c.property
  have hv := TwelveCellCertificate.unit_interval_of_valid (twelveLayerCellTable_all_valid c.val hc)
  have hr : (c.val.right : ℝ) ≤ 1 := by exact_mod_cast hv.2.2
  have hlr : (c.val.left : ℝ) < (c.val.right : ℝ) := by exact_mod_cast hv.2.1
  have hw : (c.val.value : ℝ) ≤ 17 := by exact_mod_cast (selectedCell_predicate c.property).2.1
  have hw0 : (0 : ℝ) ≤ c.val.value := Nat.cast_nonneg _
  have hg := periodGap_shrink_loss r (selectedCell_left_lower c) hr hlr
    cellShrinkEpsilon_pos cellShrinkEpsilon_lt_half
  change periodGap r (c.val.left : ℝ) (c.val.right : ℝ) -
    periodGap r (selectedCellTemplate c).a (selectedCellTemplate c).b ≤
      2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon at hg
  have hm := mul_le_mul_of_nonneg_left hg hw0
  have heps := cellShrinkEpsilon_pos
  have he : 0 ≤ 2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon := by positivity
  have hw' := mul_le_mul_of_nonneg_right hw he
  nlinarith

/-- Uniform finite-period loss; no iteration over `K` is performed. -/
theorem selectedCellTemplate_rate_lower (K : ℕ) :
    selectedUnshrunkRate K -
        (2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon * K * 17 * 1180 / 69) ≤
      periodWindowRate K selectedCellSet selectedCellTemplate := by
  have hcard : (selectedCellSet.card : ℝ) ≤ 1180 := by exact_mod_cast selectedCellSet_card_le
  have hcell (r : ℕ) :
      (∑ c ∈ selectedCellSet,
        (c.val.value : ℝ) * periodGap r (c.val.left : ℝ) (c.val.right : ℝ)) ≤
      (∑ c ∈ selectedCellSet,
        (c.val.value : ℝ) * periodGap r (selectedCellTemplate c).a (selectedCellTemplate c).b) +
        17 * (2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon) * 1180 := by
    have h := Finset.sum_le_sum (s := selectedCellSet) (fun c _ => selectedCell_gap_le r c)
    rw [Finset.sum_add_distrib] at h
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    have heps := cellShrinkEpsilon_pos
    have he : 0 ≤ 17 * (2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon) := by positivity
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.range K) (fun r _ => hcell r)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  unfold selectedUnshrunkRate periodWindowRate
  simp only [selectedCellTemplate_cell]
  nlinarith

end OddPiPowers.PrimeRates
