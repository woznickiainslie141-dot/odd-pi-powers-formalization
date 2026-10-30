module

public import OddPiPowers.Analysis.HorizontalKernelIntegrable
public import OddPiPowers.Arithmetic.TwelveLayerFamily

/-! End-to-end whole-line domination for every actual row of the
17-interval twelve-layer family, at every positive scale. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem twelveLayer_denominator_degree_lower (N : ℕ) :
    69 * N + 1 ≤ (twelveLayerActualFamily N).denominator.natDegree := by
  exact (twelveLayerActualFamily N).denominator_natDegree_ge_n_add_one
    (0 : Fin 17) (by rfl)

theorem twelveLayer_horizontal_degree (N : ℕ) (hN : 0 < N) :
    2 * (16 + 2) ≤ (twelveLayerActualFamily N).denominator.natDegree := by
  have h := twelveLayer_denominator_degree_lower N
  omega

theorem twelveLayer_horizontal_integrable (N : ℕ) (hN : 0 < N)
    (Y : ℝ) (hY : 1 / 2 < Y) (h : Fin 17) :
    Integrable ((twelveLayerActualFamily N).horizontalKernel h.val Y) ∧
      Integrable ((twelveLayerActualFamily N).horizontalKernel h.val (-Y)) := by
  have hn : 0 < (twelveLayerActualFamily N).n := by
    change 0 < 69 * N
    omega
  have hh : h.val ≤ 16 := by omega
  exact ⟨(twelveLayerActualFamily N).integrable_horizontalKernel hn Y hY 16 h.val hh
    (twelveLayer_horizontal_degree N hN),
    (twelveLayerActualFamily N).integrable_horizontalKernel_lower hn Y hY 16 h.val hh
    (twelveLayer_horizontal_degree N hN)⟩

/-- The same integrable function dominates both horizontal lines, every row,
and every positive scale N. It has no dependence on a rational approximant. -/
theorem twelveLayer_horizontal_uniform_majorant (Y : ℝ) (hY : 1 / 2 < Y) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ N : ℕ, 0 < N → ∀ h : Fin 17, ∀ t : ℝ,
        ‖(twelveLayerActualFamily N).normalizedHorizontalKernel h.val Y t‖ ≤ g t ∧
        ‖(twelveLayerActualFamily N).normalizedHorizontalKernel h.val (-Y) t‖ ≤ g t := by
  refine ⟨horizontalMajorant (horizontalB Y) (Y + 1 / 2) 16,
    integrable_horizontalMajorant (horizontalB_pos hY) (by linarith) 16, ?_⟩
  intro N hN h t
  have hn : 0 < (twelveLayerActualFamily N).n := by
    change 0 < 69 * N
    omega
  have hh : h.val ≤ 16 := by omega
  exact ⟨(twelveLayerActualFamily N).normalizedHorizontalKernel_bound hn Y t hY 16 h.val hh
    (twelveLayer_horizontal_degree N hN),
    (twelveLayerActualFamily N).normalizedHorizontalKernel_lower_bound hn Y t hY 16 h.val hh
    (twelveLayer_horizontal_degree N hN)⟩

end OddPiPowers
