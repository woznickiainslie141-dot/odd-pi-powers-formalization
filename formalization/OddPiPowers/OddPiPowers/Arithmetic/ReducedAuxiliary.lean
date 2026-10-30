module

public import OddPiPowers.Arithmetic.ActualCoefficientDivisor

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped BigOperators

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

/-- Divide every coefficient of the actual integer auxiliary polynomial by
the common positive prime-power factor. -/
noncomputable def reducedAuxiliaryInt (h j : Fin M) : Polynomial ℤ :=
  ∑ k ∈ (actualAuxiliaryInt P h j).support,
    C (((actualAuxiliaryInt P h j).coeff k) /
      (P.actualAuxiliaryPrimeDivisor : ℤ)) * X ^ k

theorem reducedAuxiliaryInt_mul (h j : Fin M) :
    C (P.actualAuxiliaryPrimeDivisor : ℤ) * P.reducedAuxiliaryInt h j =
      actualAuxiliaryInt P h j := by
  classical
  ext k
  rw [Polynomial.coeff_C_mul, reducedAuxiliaryInt, Polynomial.finsetSum_coeff]
  by_cases hk : k ∈ (actualAuxiliaryInt P h j).support
  · rw [Finset.sum_eq_single_of_mem k hk]
    · rw [Polynomial.coeff_C_mul_X_pow]
      simp only [if_pos rfl, mul_one]
      have hdvd := P.actualAuxiliaryPrimeDivisor_dvd_intCoeff (h := h) (j := j) k
      have hD : (P.actualAuxiliaryPrimeDivisor : ℤ) ≠ 0 := by
        exact_mod_cast (ne_of_gt P.actualAuxiliaryPrimeDivisor_pos)
      obtain ⟨q, hq⟩ := hdvd
      calc
        (P.actualAuxiliaryPrimeDivisor : ℤ) *
            (((actualAuxiliaryInt P h j).coeff k) /
              (P.actualAuxiliaryPrimeDivisor : ℤ)) =
            (P.actualAuxiliaryPrimeDivisor : ℤ) *
              (((P.actualAuxiliaryPrimeDivisor : ℤ) * q) /
                (P.actualAuxiliaryPrimeDivisor : ℤ)) := by rw [hq]
        _ = (P.actualAuxiliaryPrimeDivisor : ℤ) * q := by
              rw [Int.mul_ediv_cancel_left _ hD]
        _ = (actualAuxiliaryInt P h j).coeff k := hq.symm
    · intro i hi hik
      rw [Polynomial.coeff_C_mul_X_pow]
      simp [Ne.symm hik]
  · rw [Finset.sum_eq_zero]
    · have hk0 : (actualAuxiliaryInt P h j).coeff k = 0 := by
        simpa [Polynomial.mem_support_iff] using hk
      exact hk0.symm
    · intro i hi
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases hki : k = i
      · subst i
        exact (hk hi).elim
      · simp [hki]

noncomputable def actualAuxiliaryIntEvalI : Polynomial ℤ →+* ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℂ) Complex.I

theorem actualAuxiliaryInt_evalI (h j : Fin M) :
    actualAuxiliaryIntEvalI (actualAuxiliaryInt P h j) =
      actualAuxiliaryPolynomialEvalI (actualAuxiliary P h j) := by
  have hmap :
      Polynomial.map (Int.castRingHom ℂ) (actualAuxiliaryInt P h j) =
        Polynomial.map (Rat.castHom ℂ) (actualAuxiliary P h j) := by
    calc
      _ = Polynomial.map (Rat.castHom ℂ)
            (Polynomial.map (Int.castRingHom ℚ) (actualAuxiliaryInt P h j)) := by
              calc
                _ = Polynomial.map
                      ((Rat.castHom ℂ).comp (Int.castRingHom ℚ))
                      (actualAuxiliaryInt P h j) := by
                        congr 1
                _ = _ := by rw [Polynomial.map_map]
      _ = _ := by rw [map_actualAuxiliaryInt]
  have heval := congrArg (fun f : Polynomial ℂ => f.eval Complex.I) hmap
  simpa [actualAuxiliaryIntEvalI, actualAuxiliaryPolynomialEvalI,
    Polynomial.eval_map] using heval

noncomputable def reducedAuxiliaryIntMatrixAtI : Matrix (Fin M) (Fin M) ℂ :=
  fun h j => actualAuxiliaryIntEvalI (P.reducedAuxiliaryInt h j)

theorem reducedAuxiliaryIntMatrixAtI_smul :
    ((P.actualAuxiliaryPrimeDivisor : ℤ) : ℂ) •
        P.reducedAuxiliaryIntMatrixAtI =
      actualAuxiliaryPolynomialMatrixAtI P := by
  ext h j
  change ((P.actualAuxiliaryPrimeDivisor : ℤ) : ℂ) *
      actualAuxiliaryIntEvalI (P.reducedAuxiliaryInt h j) =
    actualAuxiliaryPolynomialEvalI (actualAuxiliary P h j)
  calc
    _ = actualAuxiliaryIntEvalI
          (C (P.actualAuxiliaryPrimeDivisor : ℤ) * P.reducedAuxiliaryInt h j) := by
            simp [actualAuxiliaryIntEvalI]
    _ = actualAuxiliaryIntEvalI (actualAuxiliaryInt P h j) := by
          rw [P.reducedAuxiliaryInt_mul h j]
    _ = actualAuxiliaryPolynomialEvalI (actualAuxiliary P h j) :=
          P.actualAuxiliaryInt_evalI h j

theorem reducedAuxiliaryIntMatrixAtI_det_ne_zero :
    Matrix.det P.reducedAuxiliaryIntMatrixAtI ≠ (0 : ℂ) := by
  have hscale := P.reducedAuxiliaryIntMatrixAtI_smul
  have hdet :
      ((P.actualAuxiliaryPrimeDivisor : ℤ) : ℂ) ^ M *
          Matrix.det P.reducedAuxiliaryIntMatrixAtI =
        Matrix.det (actualAuxiliaryPolynomialMatrixAtI P) := by
    calc
      _ = Matrix.det
            (((P.actualAuxiliaryPrimeDivisor : ℤ) : ℂ) •
              P.reducedAuxiliaryIntMatrixAtI) := by
            rw [Matrix.det_smul]
            simp
      _ = Matrix.det (actualAuxiliaryPolynomialMatrixAtI P) := by rw [hscale]
  have hactual := actualAuxiliaryPolynomialMatrixAtI_det_ne_zero P
  intro hz
  have hzero :
      ((P.actualAuxiliaryPrimeDivisor : ℤ) : ℂ) ^ M *
          Matrix.det P.reducedAuxiliaryIntMatrixAtI = 0 := by simp [hz]
  rw [hdet] at hzero
  exact hactual hzero

end ActualIntervals

end OddPiPowers

end
