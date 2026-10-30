module

public import OddPiPowers.Arithmetic.TwelveLayerCellOrder
public import OddPiPowers.Arithmetic.TwelveLayerCost
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace OddPiPowers

/-- The complete finite certificate, evaluated on open cells and periodized.
The supremum also makes the definition sound before disjointness is used. -/
noncomputable def twelveLayerLowerBound (z : ℝ) : ℕ := by
  classical
  exact twelveLayerCellTable.toFinset.sup (fun c =>
    if (c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ)
    then c.value else 0)

theorem twelveLayerLowerBound_le_cost (z y : ℝ) :
    twelveLayerLowerBound z ≤ twelveLayerShape.cost z y := by
  classical
  unfold twelveLayerLowerBound
  apply Finset.sup_le
  intro c hc
  by_cases h : (c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ)
  · simp only [if_pos h]
    have hvalue := twelveLayerCell_cost_ge_value c
      (twelveLayerCellTable_all_valid c (List.mem_toFinset.mp hc))
      (y := y) h.1 h.2
    simpa only [CarryShape.cost_fract_z] using hvalue
  · simp only [if_neg h]
    exact Nat.zero_le _

theorem twelveLayerLowerBound_add_int (z : ℝ) (k : ℤ) :
    twelveLayerLowerBound (z + k) = twelveLayerLowerBound z := by
  classical
  simp only [twelveLayerLowerBound, Int.fract_add_intCast]

theorem twelveLayerLowerBound_scale_le_cost (s : ℕ) (z y : ℝ) :
    s * twelveLayerLowerBound z ≤ (twelveLayerShape.scaleWeights s).cost z y :=
  twelveLayerShape.cost_scaleWeights_ge s (twelveLayerLowerBound z) z y
    (twelveLayerLowerBound_le_cost z y)

theorem twelveLayerLowerBound_eq_zero_of_outside (z : ℝ)
    (h : ∀ c ∈ twelveLayerCellTable,
      ¬ ((c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ))) :
    twelveLayerLowerBound z = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold twelveLayerLowerBound
  apply Finset.sup_le
  intro c hc
  simp only [if_neg (h c (List.mem_toFinset.mp hc)), le_refl]

theorem twelveLayerCell_value_le_lowerBound (c : TwelveCellCertificate)
    (hc : c ∈ twelveLayerCellTable) {z : ℝ}
    (hzl : (c.left : ℝ) < Int.fract z) (hzr : Int.fract z < (c.right : ℝ)) :
    c.value ≤ twelveLayerLowerBound z := by
  classical
  unfold twelveLayerLowerBound
  have hs := Finset.le_sup (s := twelveLayerCellTable.toFinset)
    (f := fun d => if (d.left : ℝ) < Int.fract z ∧ Int.fract z < (d.right : ℝ)
      then d.value else 0) (List.mem_toFinset.mpr hc)
  have hcell : (c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ) := ⟨hzl, hzr⟩
  simpa only [if_pos hcell] using hs

theorem twelveLayerLowerBound_eq_zero_of_endpoint (c : TwelveCellCertificate)
    (hc : c ∈ twelveLayerCellTable) (z : ℝ)
    (hz : Int.fract z = (c.left : ℝ) ∨ Int.fract z = (c.right : ℝ)) :
    twelveLayerLowerBound z = 0 := by
  apply twelveLayerLowerBound_eq_zero_of_outside
  intro d hd hinside
  have hclt : (c.left : ℝ) < (c.right : ℝ) := by
    exact_mod_cast (TwelveCellCertificate.unit_interval_of_valid
      (twelveLayerCellTable_all_valid c hc)).2.1
  rcases twelveLayerCellTable_compare hc hd with heq | hcd | hdc
  · subst d
    rcases hz with hz | hz <;> linarith [hinside.1, hinside.2]
  · have horder : (c.right : ℝ) ≤ (d.left : ℝ) := by exact_mod_cast hcd
    rcases hz with hz | hz <;> linarith [hinside.1, hinside.2]
  · have horder : (d.right : ℝ) ≤ (c.left : ℝ) := by exact_mod_cast hdc
    rcases hz with hz | hz <;> linarith [hinside.1, hinside.2]

theorem twelveLayerLowerBound_nontrivial :
    6 ≤ twelveLayerLowerBound (137 / 9384) := by
  let c : TwelveCellCertificate :=
    { leftNumerator := 1, leftDenominator := 69,
      rightNumerator := 1, rightDenominator := 68,
      rankCode := 111039596418616124727684240453360,
      orderCode := 1273226025159533994039293277479016,
      floorCode := 2736874734008091634300000000000000000000000,
      value := 6 }
  have hc0 : c ∈ twelveLayerCellChunk0 := by decide
  have hc : c ∈ twelveLayerCellTable := by
    simp only [twelveLayerCellTable, List.mem_append, hc0, true_or]
  have hlo : (c.left : ℝ) < Int.fract (137 / 9384) := by
    norm_num [c, TwelveCellCertificate.left, Int.fract]
  have hhi : Int.fract (137 / 9384) < (c.right : ℝ) := by
    norm_num [c, TwelveCellCertificate.right, Int.fract]
  exact twelveLayerCell_value_le_lowerBound c hc hlo hhi

end OddPiPowers

end
