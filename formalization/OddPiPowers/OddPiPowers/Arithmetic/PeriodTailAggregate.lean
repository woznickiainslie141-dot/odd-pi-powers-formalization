module

public import OddPiPowers.Arithmetic.PeriodTailFloor
public import OddPiPowers.Arithmetic.PeriodPrefixSum

/-! Draft finite sum of tail certificates for the selected actual cells.
No numerical certificate is evaluated in this file. -/

@[expose] public section

open scoped BigOperators

namespace OddPiPowers.PrimeRates

noncomputable def selectedTailRationalSum (T K : ℕ) : ℝ :=
  (selectedCells.map (fun c => (periodTailRational T K c : ℝ))).sum

theorem selectedTailRationalSum_le (T K : ℕ) (hT : 1 ≤ T) (hTK : T ≤ K) :
    selectedTailRationalSum T K ≤
      (1 / 69 : ℝ) * ∑ r ∈ Finset.Ico T K, ∑ c ∈ selectedCellSet,
        (c.val.value : ℝ) * periodGap r (c.val.left : ℝ) (c.val.right : ℝ) := by
  classical
  unfold selectedTailRationalSum
  rw [← List.sum_toFinset _ selectedCells_nodup]
  rw [← selectedCellSet_sum_val (fun c => (periodTailRational T K c : ℝ))]
  have hbound : (∑ c ∈ selectedCellSet, (periodTailRational T K c.val : ℝ)) ≤
      ∑ c ∈ selectedCellSet, (c.val.value : ℝ) / 69 *
        ∑ r ∈ Finset.Ico T K, periodGap r (c.val.left : ℝ) (c.val.right : ℝ) := by
    apply Finset.sum_le_sum
    intro c hc
    have ha : (0 : ℝ) < (c.val.left : ℝ) := by
      have hl := selectedCell_left_lower c
      linarith
    have hab : (c.val.left : ℝ) < (c.val.right : ℝ) := by
      exact_mod_cast (TwelveCellCertificate.unit_interval_of_valid
        (twelveLayerCellTable_all_valid c.val (selectedCell_mem_table c.property))).2.1
    exact periodTailRational_le T K hT hTK c.val ha hab
  calc
    _ ≤ _ := hbound
    _ = (1 / 69 : ℝ) * ∑ r ∈ Finset.Ico T K, ∑ c ∈ selectedCellSet,
        (c.val.value : ℝ) * periodGap r (c.val.left : ℝ) (c.val.right : ℝ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro c hc
      ring

theorem selectedUnshrunkRate_add_tail (T K : ℕ) (hT : 1 ≤ T) (hTK : T ≤ K) :
    selectedUnshrunkRate T + selectedTailRationalSum T K ≤ selectedUnshrunkRate K := by
  have ht := selectedTailRationalSum_le T K hT hTK
  have hsplit : selectedUnshrunkRate T +
      (1 / 69 : ℝ) * ∑ r ∈ Finset.Ico T K, ∑ c ∈ selectedCellSet,
        (c.val.value : ℝ) * periodGap r (c.val.left : ℝ) (c.val.right : ℝ) =
      selectedUnshrunkRate K := by
    unfold selectedUnshrunkRate
    rw [← mul_add, Finset.sum_range_add_sum_Ico _ hTK]
  linarith

/-- Combine any independently proved prefix and tail lower bounds with the
actual shrunken-window loss. -/
theorem selectedTemplateRate_ge_prefix_add_tail (T K : ℕ) (hT : 1 ≤ T) (hTK : T ≤ K)
    (prefixLower tailLower : ℝ)
    (hp : prefixLower ≤ selectedUnshrunkRate T)
    (ht : tailLower ≤ selectedTailRationalSum T K) :
    prefixLower + tailLower -
        (2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon * K * 17 * 1180 / 69) ≤
      periodWindowRate K selectedCellSet selectedCellTemplate := by
  have hfull := selectedUnshrunkRate_add_tail T K hT hTK
  have hshrink := selectedCellTemplate_rate_lower K
  linarith

/-- List-based prefix certificates can supply the same bound directly. -/
theorem selectedTemplateRate_ge_label_prefix_add_tail (T K : ℕ)
    (hT : 1 ≤ T) (hTK : T ≤ K) (prefixLower tailLower : ℝ)
    (hp : prefixLower ≤ ((periodPrefixLabels T selectedCells).map periodLabelActual).sum)
    (ht : tailLower ≤ selectedTailRationalSum T K) :
    prefixLower + tailLower -
        (2 * (69 : ℝ) ^ 2 * cellShrinkEpsilon * K * 17 * 1180 / 69) ≤
      periodWindowRate K selectedCellSet selectedCellTemplate := by
  apply selectedTemplateRate_ge_prefix_add_tail T K hT hTK prefixLower tailLower
  · simpa only [selected_periodPrefixLabels_actual_sum] using hp
  · exact ht

end OddPiPowers.PrimeRates
