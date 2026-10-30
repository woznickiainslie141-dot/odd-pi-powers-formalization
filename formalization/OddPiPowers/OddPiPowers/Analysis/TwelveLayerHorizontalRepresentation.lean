module

public import OddPiPowers.Analysis.ActualHorizontalRepresentation
public import OddPiPowers.Analysis.TwelveLayerContour

/-! Complete infinite-horizontal representation for every actual base row. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem twelveLayer_finitePoleContour_eq_horizontal (N : ℕ) (hN : 0 < N)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (h : Fin 17) :
    (twelveLayerActualFamily N).finitePoleContour h.val (Complex.I * (theta : ℂ)) =
      ((69 * N : ℕ) : ℂ) *
        ((∫ t : ℝ, (twelveLayerActualFamily N).meromorphicExponentialKernel h.val
          (Complex.I * (theta : ℂ)) (horizontalPoint (69 * N) (-Y) t)) -
         (∫ t : ℝ, (twelveLayerActualFamily N).meromorphicExponentialKernel h.val
          (Complex.I * (theta : ℂ)) (horizontalPoint (69 * N) Y t))) := by
  have hn : 0 < (twelveLayerActualFamily N).n := by change 0 < 69 * N; omega
  exact (twelveLayerActualFamily N).finitePoleContour_eq_horizontal h (by norm_num) hn
    theta Y hY 16 (by omega) (twelveLayer_horizontal_degree N hN)

theorem twelveLayer_actualAuxiliaryAtI_eq_horizontal (N : ℕ) (hN : 0 < N)
    (Y : ℝ) (hY : 1 / 2 < Y) (h : Fin 17) :
    (∑ j : Fin 17, (actualAuxiliary (twelveLayerActualFamily N) h j).eval₂
      (Rat.castHom ℂ) Complex.I * lambda ^ j.val) =
      (((auxiliaryCommonScale 17 (69 * N) : ℚ) : ℂ) / (2 * Real.pi * Complex.I)) *
        ((69 * N : ℕ) : ℂ) *
          ((∫ t : ℝ, (twelveLayerActualFamily N).meromorphicExponentialKernel h.val lambda
            (horizontalPoint (69 * N) (-Y) t)) -
           (∫ t : ℝ, (twelveLayerActualFamily N).meromorphicExponentialKernel h.val lambda
            (horizontalPoint (69 * N) Y t))) := by
  have hn : 0 < (twelveLayerActualFamily N).n := by change 0 < 69 * N; omega
  exact actualAuxiliaryAtI_eq_horizontal (twelveLayerActualFamily N) h (by norm_num) hn
    Y hY 16 (by omega) (twelveLayer_horizontal_degree N hN)

end OddPiPowers
