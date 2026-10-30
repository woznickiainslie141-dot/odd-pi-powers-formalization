module

public import OddPiPowers.Arithmetic.CellPrimeWindows
public import OddPiPowers.Arithmetic.PrimeDivisorRates

@[expose] public section

namespace OddPiPowers.PrimeRates

/-- The first positive cell in the complete twelve-layer table. -/
def calibrationCell : TwelveCellCertificate :=
  { leftNumerator := 1, leftDenominator := 69,
    rightNumerator := 1, rightDenominator := 68,
    rankCode := 111039596418616124727684240453360,
    orderCode := 1273226025159533994039293277479016,
    floorCode := 2736874734008091634300000000000000000000000,
    value := 6 }

theorem calibrationCell_mem : calibrationCell ∈ twelveLayerCellTable := by
  have hc0 : calibrationCell ∈ twelveLayerCellChunk0 := by decide
  simp only [twelveLayerCellTable, List.mem_append, hc0, true_or]

noncomputable def calibrationWindow : CertifiedCellWindow where
  cell := calibrationCell
  mem_table := calibrationCell_mem
  period := 0
  a := 3 / 206
  b := 3 / 205
  left_lt := by norm_num [calibrationCell, TwelveCellCertificate.left]
  a_lt_b := by norm_num
  right_gt := by norm_num [calibrationCell, TwelveCellCertificate.right]

theorem calibrationWindow_cap : 1 ≤ (69 : ℝ) * calibrationWindow.toWindow.lower := by
  norm_num [calibrationWindow, CertifiedCellWindow.toWindow]

theorem calibrationWindow_rate :
    finiteWindowRate ({()} : Finset Unit) (fun _ => calibrationWindow.toWindow) 69 = 2 / 69 := by
  norm_num [finiteWindowRate, calibrationWindow, CertifiedCellWindow.toWindow, calibrationCell]

theorem calibrationWindow_sum_le (z : ℝ) :
    windowWeightSum ({()} : Finset Unit) (fun _ => calibrationWindow.toWindow) z ≤
      twelveLayerLowerBound z := by
  apply certifiedCellWindows_sum_le
  intro i hi j hj h
  exact Subsingleton.elim i j

/-- A deliberately conservative positive lower rate. This does not evaluate
the much larger sum over all certified cells and many periods. -/
theorem calibration_primeCertificate_eventually_exp_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (((2 : ℝ) / 69 - η) * (69 * N : ℕ)) ≤
        (primeCertificate 69 N twelveLayerLowerBound : ℝ) := by
  have h := primeCertificate_eventually_exp_lower ({()} : Finset Unit)
    (fun _ => calibrationWindow.toWindow) 69 (by decide) twelveLayerLowerBound
    (fun i hi => calibrationWindow_cap) calibrationWindow_sum_le hη
  simpa only [calibrationWindow_rate] using h

end OddPiPowers.PrimeRates

end
