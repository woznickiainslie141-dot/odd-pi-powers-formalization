module

public import OddPiPowers.Analysis.ReducedCentralBound
public import OddPiPowers.Analysis.CentralLogProducts

/-! An exact logarithmic central majorant for the actual reduced rows.
There is no assumed limiting rate in this statement. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem reducedAuxiliaryRow_norm_le_exp_central (h : Fin M) (hM : 0 < M)
    (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y) (m : ℕ) (hh : h.val ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.reducedAuxiliaryRow h lambda‖ ≤ Real.exp (
      Real.log (((auxiliaryCommonScale M P.n : ℚ) : ℝ)) +
        Real.log (horizontalMajorantConstant (horizontalB Y) (Y + 1 / 2) m) +
          ((m + 1 : ℕ) : ℝ) * Real.log (P.n : ℝ) +
            |Real.pi / 2| * ((P.n : ℝ) * Y) + P.centralLogRatio Y -
              Real.log (P.actualAuxiliaryPrimeDivisor : ℝ)) := by
  have hD : (0 : ℝ) < P.actualAuxiliaryPrimeDivisor := by
    exact_mod_cast P.actualAuxiliaryPrimeDivisor_pos
  rw [← P.log_centralRemainderBound hn m m (Real.pi / 2) Y hY,
    Real.exp_sub, Real.exp_log (P.centralRemainderBound_pos hn m m (Real.pi / 2) Y hY),
    Real.exp_log hD]
  exact P.reducedAuxiliaryRow_norm_le_central h hM hn Y hY m hh hd

end OddPiPowers.ActualIntervals
