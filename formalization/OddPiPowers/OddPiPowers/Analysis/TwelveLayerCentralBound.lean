module

public import OddPiPowers.Analysis.ReducedCentralLogBound
public import OddPiPowers.Analysis.TwelveLayerHorizontalRepresentation

/-! The explicit central estimate for all seventeen actual base rows. -/

@[expose] public section

namespace OddPiPowers

theorem twelveLayer_actualAuxiliaryAtI_norm_le_central (N : ℕ) (hN : 0 < N)
    (Y : ℝ) (hY : 1 / 2 < Y) (h : Fin 17) :
    ‖∑ j : Fin 17, (actualAuxiliary (twelveLayerActualFamily N) h j).eval₂
      (Rat.castHom ℂ) Complex.I * lambda ^ j.val‖ ≤
      (twelveLayerActualFamily N).centralRemainderBound 16 16 (Real.pi / 2) Y := by
  have hn : 0 < (twelveLayerActualFamily N).n := by change 0 < 69 * N; omega
  exact actualAuxiliaryAtI_norm_le_central (twelveLayerActualFamily N) h (by norm_num)
    hn Y hY 16 (by omega) (twelveLayer_horizontal_degree N hN)

theorem twelveLayer_reducedAuxiliaryRow_norm_le_central (N : ℕ) (hN : 0 < N)
    (Y : ℝ) (hY : 1 / 2 < Y) (h : Fin 17) :
    ‖(twelveLayerActualFamily N).reducedAuxiliaryRow h lambda‖ ≤
      (twelveLayerActualFamily N).centralRemainderBound 16 16 (Real.pi / 2) Y /
        ((twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor : ℝ) := by
  have hn : 0 < (twelveLayerActualFamily N).n := by change 0 < 69 * N; omega
  exact (twelveLayerActualFamily N).reducedAuxiliaryRow_norm_le_central h (by norm_num)
    hn Y hY 16 (by omega) (twelveLayer_horizontal_degree N hN)

end OddPiPowers
