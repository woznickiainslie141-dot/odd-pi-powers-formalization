module

public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellOrder
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCost
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace OddPiPowers.L99

/-- The complete finite certificate, evaluated on open cells and periodized.
The supremum also makes the definition sound before disjointness is used. -/
noncomputable def twentyEightLayerLowerBound (z : ℝ) : ℕ := by
  classical
  exact twentyEightLayerCellTable.toFinset.sup (fun c =>
    if (c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ)
    then c.value else 0)

theorem twentyEightLayerLowerBound_le_cost (z y : ℝ) :
    twentyEightLayerLowerBound z ≤ twentyEightLayerShape.cost z y := by
  classical
  unfold twentyEightLayerLowerBound
  apply Finset.sup_le
  intro c hc
  by_cases h : (c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ)
  · simp only [if_pos h]
    have hvalue := twentyEightLayerCell_cost_ge_value c
      (twentyEightLayerCellTable_all_valid c (List.mem_toFinset.mp hc))
      (y := y) h.1 h.2
    simpa only [CarryShape.cost_fract_z] using hvalue
  · simp only [if_neg h]
    exact Nat.zero_le _

theorem twentyEightLayerLowerBound_add_int (z : ℝ) (k : ℤ) :
    twentyEightLayerLowerBound (z + k) = twentyEightLayerLowerBound z := by
  classical
  simp only [twentyEightLayerLowerBound, Int.fract_add_intCast]

theorem twentyEightLayerLowerBound_scale_le_cost (s : ℕ) (z y : ℝ) :
    s * twentyEightLayerLowerBound z ≤ (twentyEightLayerShape.scaleWeights s).cost z y :=
  twentyEightLayerShape.cost_scaleWeights_ge s (twentyEightLayerLowerBound z) z y
    (twentyEightLayerLowerBound_le_cost z y)

theorem twentyEightLayerLowerBound_eq_zero_of_outside (z : ℝ)
    (h : ∀ c ∈ twentyEightLayerCellTable,
      ¬ ((c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ))) :
    twentyEightLayerLowerBound z = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold twentyEightLayerLowerBound
  apply Finset.sup_le
  intro c hc
  simp only [if_neg (h c (List.mem_toFinset.mp hc)), le_refl]

theorem twentyEightLayerCell_value_le_lowerBound (c : TwentyEightCellCertificate)
    (hc : c ∈ twentyEightLayerCellTable) {z : ℝ}
    (hzl : (c.left : ℝ) < Int.fract z) (hzr : Int.fract z < (c.right : ℝ)) :
    c.value ≤ twentyEightLayerLowerBound z := by
  classical
  unfold twentyEightLayerLowerBound
  have hs := Finset.le_sup (s := twentyEightLayerCellTable.toFinset)
    (f := fun d => if (d.left : ℝ) < Int.fract z ∧ Int.fract z < (d.right : ℝ)
      then d.value else 0) (List.mem_toFinset.mpr hc)
  have hcell : (c.left : ℝ) < Int.fract z ∧ Int.fract z < (c.right : ℝ) := ⟨hzl, hzr⟩
  simpa only [if_pos hcell] using hs

theorem twentyEightLayerLowerBound_eq_zero_of_endpoint (c : TwentyEightCellCertificate)
    (hc : c ∈ twentyEightLayerCellTable) (z : ℝ)
    (hz : Int.fract z = (c.left : ℝ) ∨ Int.fract z = (c.right : ℝ)) :
    twentyEightLayerLowerBound z = 0 := by
  apply twentyEightLayerLowerBound_eq_zero_of_outside
  intro d hd hinside
  have hclt : (c.left : ℝ) < (c.right : ℝ) := by
    exact_mod_cast (TwentyEightCellCertificate.unit_interval_of_valid
      (twentyEightLayerCellTable_all_valid c hc)).2.1
  rcases twentyEightLayerCellTable_compare hc hd with heq | hcd | hdc
  · subst d
    rcases hz with hz | hz <;> linarith [hinside.1, hinside.2]
  · have horder : (c.right : ℝ) ≤ (d.left : ℝ) := by exact_mod_cast hcd
    rcases hz with hz | hz <;> linarith [hinside.1, hinside.2]
  · have horder : (d.right : ℝ) ≤ (c.left : ℝ) := by exact_mod_cast hdc
    rcases hz with hz | hz <;> linarith [hinside.1, hinside.2]

end OddPiPowers.L99
end
