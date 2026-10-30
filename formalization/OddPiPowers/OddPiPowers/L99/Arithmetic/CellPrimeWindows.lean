module

public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCertifiedBound
public import OddPiPowers.Arithmetic.FiniteWindowCover
public import OddPiPowers.Arithmetic.FinitePeriodKernel

@[expose] public section

open scoped BigOperators

namespace OddPiPowers.L99.PrimeRates

open OddPiPowers.PrimeRates

/-- A strictly interior interval in any of the 3004 accepted carry cells,
translated by a fixed nonnegative integer period. -/
structure CertifiedCellWindow where
  cell : TwentyEightCellCertificate
  mem_table : cell ∈ twentyEightLayerCellTable
  period : ℕ
  a : ℝ
  b : ℝ
  left_lt : (cell.left : ℝ) < a
  a_lt_b : a < b
  right_gt : b < (cell.right : ℝ)

theorem CertifiedCellWindow.unit_bounds (V : CertifiedCellWindow) :
    0 < V.a ∧ V.a < V.b ∧ V.b < 1 := by
  have hb := TwentyEightCellCertificate.unit_interval_of_valid
    (twentyEightLayerCellTable_all_valid V.cell V.mem_table)
  have hl : (0 : ℝ) ≤ (V.cell.left : ℝ) := by exact_mod_cast hb.1
  have hr : (V.cell.right : ℝ) ≤ 1 := by exact_mod_cast hb.2.2
  exact ⟨hl.trans_lt V.left_lt, V.a_lt_b, V.right_gt.trans_le hr⟩

noncomputable def CertifiedCellWindow.toWindow (V : CertifiedCellWindow) : PrimeWindow where
  lower := (V.period : ℝ) + V.a
  upper := (V.period : ℝ) + V.b
  weight := V.cell.value
  lower_pos := add_pos_of_nonneg_of_pos (Nat.cast_nonneg V.period) V.unit_bounds.1
  lower_lt_upper := by linarith [V.a_lt_b]

theorem CertifiedCellWindow.local_bound (V : CertifiedCellWindow) (z : ℝ)
    (hlo : V.toWindow.lower ≤ z) (hhi : z < V.toWindow.upper) :
    V.toWindow.weight ≤ twentyEightLayerLowerBound z := by
  have hunit : 0 ≤ z - (V.period : ℝ) ∧ z - (V.period : ℝ) < 1 := by
    change (V.period : ℝ) + V.a ≤ z at hlo
    change z < (V.period : ℝ) + V.b at hhi
    constructor <;> linarith [V.unit_bounds.1, V.unit_bounds.2.2]
  have hfract : Int.fract z = z - (V.period : ℝ) := by
    calc
      Int.fract z = Int.fract ((z - (V.period : ℝ)) + (V.period : ℝ)) := by congr 1; ring
      _ = Int.fract (z - (V.period : ℝ)) := Int.fract_add_natCast _ _
      _ = _ := Int.fract_eq_self.mpr hunit
  apply twentyEightLayerCell_value_le_lowerBound V.cell V.mem_table
  · rw [hfract]
    change (V.period : ℝ) + V.a ≤ z at hlo
    linarith [V.left_lt]
  · rw [hfract]
    change z < (V.period : ℝ) + V.b at hhi
    linarith [V.right_gt]

theorem CertifiedCellWindow.rate_identity (V : CertifiedCellWindow) :
    (V.toWindow.weight : ℝ) * (1 / V.toWindow.lower - 1 / V.toWindow.upper) =
      V.cell.value * periodGap V.period V.a V.b := rfl

/-- Separation is inherited from distinct periods and the accepted ordered
cell table. Only injectivity of the (period, cell) labels is needed. -/
theorem CertifiedCellWindow.separated (V U : CertifiedCellWindow)
    (hne : (V.period, V.cell) ≠ (U.period, U.cell)) :
    V.toWindow.upper ≤ U.toWindow.lower ∨ U.toWindow.upper ≤ V.toWindow.lower := by
  by_cases hr : V.period = U.period
  · have hc : V.cell ≠ U.cell := by
      intro hc
      exact hne (Prod.ext hr hc)
    rcases twentyEightLayerCellTable_compare V.mem_table U.mem_table with heq | hVU | hUV
    · exact False.elim (hc heq)
    · left
      have horder : (V.cell.right : ℝ) ≤ (U.cell.left : ℝ) := by exact_mod_cast hVU
      change (V.period : ℝ) + V.b ≤ (U.period : ℝ) + U.a
      rw [hr]
      linarith [V.right_gt, U.left_lt]
    · right
      have horder : (U.cell.right : ℝ) ≤ (V.cell.left : ℝ) := by exact_mod_cast hUV
      change (U.period : ℝ) + U.b ≤ (V.period : ℝ) + V.a
      rw [hr]
      linarith [U.right_gt, V.left_lt]
  · rcases lt_or_gt_of_ne hr with hlt | hgt
    · left
      have hper : (V.period : ℝ) + 1 ≤ (U.period : ℝ) := by
        exact_mod_cast (show V.period + 1 ≤ U.period from hlt)
      change (V.period : ℝ) + V.b ≤ (U.period : ℝ) + U.a
      linarith [V.unit_bounds.2.2, U.unit_bounds.1]
    · right
      have hper : (U.period : ℝ) + 1 ≤ (V.period : ℝ) := by
        exact_mod_cast (show U.period + 1 ≤ V.period from hgt)
      change (U.period : ℝ) + U.b ≤ (V.period : ℝ) + V.a
      linarith [U.unit_bounds.2.2, V.unit_bounds.1]

theorem certifiedCellWindows_sum_le {ι : Type*} (s : Finset ι)
    (V : ι → CertifiedCellWindow)
    (hinj : Set.InjOn (fun i => ((V i).period, (V i).cell)) ↑s) (z : ℝ) :
    windowWeightSum s (fun i => (V i).toWindow) z ≤ twentyEightLayerLowerBound z := by
  apply windowWeightSum_le_of_pairwise s _ _ z
  · intro i hi j hj hne
    exact (V i).separated (V j) (fun heq => hne (hinj hi hj heq))
  · intro i hi z hlo hhi
    exact (V i).local_bound z hlo hhi

end OddPiPowers.L99.PrimeRates

end
