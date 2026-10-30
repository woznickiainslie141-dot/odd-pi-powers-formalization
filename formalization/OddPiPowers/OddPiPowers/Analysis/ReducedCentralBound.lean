module

public import OddPiPowers.Analysis.ActualCentralBound
public import OddPiPowers.Arithmetic.ReducedAuxiliary

/-! The central estimate for the actual integral Gaussian coefficient quotient. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

open scoped BigOperators

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def reducedAuxiliaryRow (h : Fin M) (z : ℂ) : ℂ :=
  ∑ j : Fin M, P.reducedAuxiliaryIntMatrixAtI h j * z ^ j.val

set_option backward.isDefEq.respectTransparency false in
theorem reducedAuxiliaryRow_mul (h : Fin M) (z : ℂ) :
    (P.actualAuxiliaryPrimeDivisor : ℂ) * P.reducedAuxiliaryRow h z =
      ∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * z ^ j.val := by
  have he (j : Fin M) :
      (P.actualAuxiliaryPrimeDivisor : ℂ) * P.reducedAuxiliaryIntMatrixAtI h j =
        (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I := by
    have ht := congrFun (congrFun P.reducedAuxiliaryIntMatrixAtI_smul h) j
    simpa only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_natCast,
      actualAuxiliaryPolynomialMatrixAtI, RingHom.mapMatrix_apply,
      actualAuxiliaryPolynomialEvalI, Polynomial.coe_eval₂RingHom,
      Matrix.map_apply, actualAuxiliaryPolynomialMatrix] using ht
  unfold reducedAuxiliaryRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, he j]

theorem reducedAuxiliaryRow_norm (h : Fin M) (z : ℂ) :
    ‖P.reducedAuxiliaryRow h z‖ =
      ‖∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) Complex.I * z ^ j.val‖ /
        (P.actualAuxiliaryPrimeDivisor : ℝ) := by
  have hD : (0 : ℝ) < P.actualAuxiliaryPrimeDivisor := by
    exact_mod_cast P.actualAuxiliaryPrimeDivisor_pos
  have he := congrArg norm (P.reducedAuxiliaryRow_mul h z)
  rw [norm_mul, Complex.norm_natCast] at he
  exact (eq_div_iff hD.ne').mpr ((mul_comm _ _).trans he)

theorem reducedAuxiliaryRow_norm_le_central (h : Fin M) (hM : 0 < M)
    (hn : 0 < P.n) (Y : ℝ) (hY : 1 / 2 < Y) (m : ℕ) (hh : h.val ≤ m)
    (hd : 2 * (m + 2) ≤ P.denominator.natDegree) :
    ‖P.reducedAuxiliaryRow h lambda‖ ≤
      P.centralRemainderBound m m (Real.pi / 2) Y / (P.actualAuxiliaryPrimeDivisor : ℝ) := by
  rw [P.reducedAuxiliaryRow_norm]
  exact div_le_div_of_nonneg_right
    (actualAuxiliaryAtI_norm_le_central P h hM hn Y hY m hh hd) (Nat.cast_nonneg _)

end OddPiPowers.ActualIntervals
