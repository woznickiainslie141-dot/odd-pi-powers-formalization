module

public import OddPiPowers.Analysis.ActualContourBounds
public import OddPiPowers.Analysis.TwelveLayerHorizontal

/-! The finite contour and all side estimates for the actual seventeen rows. -/

@[expose] public section

namespace OddPiPowers

open Filter MeasureTheory
open scoped Topology

theorem twelveLayer_finitePoleContour (N : ℕ) (h : Fin 17) :
    (∑ j : Fin 17, (actualAuxiliary (twelveLayerActualFamily N) h j).eval₂
      (Rat.castHom ℂ) Complex.I * lambda ^ j.val) =
      (((auxiliaryCommonScale 17 (69 * N) : ℚ) : ℂ) / (2 * Real.pi * Complex.I)) *
        (twelveLayerActualFamily N).finitePoleContour h.val lambda := by
  exact actualAuxiliaryAtI_eq_finitePoleContour (twelveLayerActualFamily N) h (by norm_num)

theorem twelveLayer_meromorphic_horizontal_integrable (N : ℕ) (hN : 0 < N)
    (theta Y : ℝ) (hY : 1 / 2 < Y) (h : Fin 17) :
    Integrable (fun t : ℝ => (twelveLayerActualFamily N).meromorphicExponentialKernel h.val
      (Complex.I * (theta : ℂ)) (horizontalPoint (69 * N) Y t)) ∧
    Integrable (fun t : ℝ => (twelveLayerActualFamily N).meromorphicExponentialKernel h.val
      (Complex.I * (theta : ℂ)) (horizontalPoint (69 * N) (-Y) t)) := by
  have hn : 0 < (twelveLayerActualFamily N).n := by change 0 < 69 * N; omega
  have hh : h.val ≤ 16 := by omega
  exact ⟨(twelveLayerActualFamily N).integrable_meromorphicExponentialKernel_horizontal
    hn theta Y hY 16 h.val hh (twelveLayer_horizontal_degree N hN),
    (twelveLayerActualFamily N).integrable_meromorphicExponentialKernel_horizontal_lower
    hn theta Y hY 16 h.val hh (twelveLayer_horizontal_degree N hN)⟩

theorem twelveLayer_meromorphic_vertical_tendsto (N : ℕ) (hN : 0 < N)
    (H : ℝ) (hH : 0 ≤ H) (theta : ℝ) (h : Fin 17) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in -H..H, Complex.I *
      (twelveLayerActualFamily N).meromorphicExponentialKernel h.val
        (Complex.I * (theta : ℂ)) (verticalPoint R y)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ => ∫ y : ℝ in -H..H, Complex.I *
      (twelveLayerActualFamily N).meromorphicExponentialKernel h.val
        (Complex.I * (theta : ℂ)) (verticalPoint (-R) y)) atTop (𝓝 0) := by
  have hd : h.val + 2 ≤ (twelveLayerActualFamily N).denominator.natDegree := by
    have ht := twelveLayer_denominator_degree_lower N
    omega
  exact ⟨(twelveLayerActualFamily N).meromorphicExponentialKernel_vertical_tendsto_right
    H hH theta h.val hd,
    (twelveLayerActualFamily N).meromorphicExponentialKernel_vertical_tendsto_left
    H hH theta h.val hd⟩

end OddPiPowers
