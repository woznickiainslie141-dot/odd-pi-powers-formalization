module

public import OddPiPowers.Transfer.Selection
public import OddPiPowers.Transfer.RateComparison

/-! Uniform comparison at one sufficiently large auxiliary scale. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

/-- For each slack there is a threshold independent of the approximation.
The row is chosen after the approximation, using only uniform disk bounds. -/
theorem auxiliary_distance_at_scale (m L k : ℕ) (D G : ℝ)
    (U : ℕ → Fin (m + 1) → GaussianInt[X]) (hfamily : AuxiliaryFamily m L D G U)
    (hG : 0 ≤ G) (hk : 0 < k) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ r, 0 < r → N ≤ L * r → ∀ (p : ℤ) (q : ℕ), 0 < q →
      ∀ θ : ℝ, θ ^ k = (p : ℝ) / q → ‖Complex.I * (θ : ℂ) / 2‖ ≤ 2 →
      (m : ℝ) * Real.log ((2 : ℝ) ^ k * q) +
          ((k - 1 : ℕ) : ℝ) * ((G + η) * (L * r : ℕ)) + Real.log 2 ≤
        (D - η) * (L * r : ℕ) →
      (1 / (((2 : ℝ) ^ k * q) ^ m *
        (Real.exp ((G + η) * (L * r : ℕ))) ^ (k - 1))) /
          (2 * Real.exp ((G + η) * (L * r : ℕ))) ≤
        ‖lambda - Complex.I * (θ : ℂ) / 2‖ := by
  obtain ⟨N, hN⟩ := hfamily.bounds η hη
  refine ⟨N, ?_⟩
  intro r hr hrN p q hq θ hθ hyDisk hscale
  obtain ⟨hsmall, hheight, hT⟩ := hN r hr hrN
  let t : ℝ := (G + η) * (L * r : ℕ)
  let H : NNReal := ⟨Real.exp t, (Real.exp_pos t).le⟩
  have hH : 1 ≤ H := by
    change (1 : ℝ) ≤ Real.exp t
    apply Real.one_le_exp
    dsimp [t]
    exact mul_nonneg (add_nonneg hG hη.le) (Nat.cast_nonneg _)
  have hheightNN : ∀ i z, ‖z‖ ≤ 2 →
      ‖((U (L * r) i).map GaussianInt.toComplex).eval z‖₊ ≤ H := by
    intro i z hz
    change ‖((U (L * r) i).map GaussianInt.toComplex).eval z‖ ≤ Real.exp t
    exact hheight i z hz
  obtain ⟨i, hi⟩ := exists_row_rational_value_lower_bound p q k hq hk θ hθ hyDisk m
    (U (L * r)) (hfamily.degree r hr) (hfamily.determinant r hr) H hH hheightNN
  let B : ℝ := (2 : ℝ) ^ k * q
  let a : ℝ := 1 / (B ^ m * (Real.exp t) ^ (k - 1))
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (pow_pos (by norm_num) _) (by exact_mod_cast hq)
  have hiR : a ≤ ‖(complexPolynomial (U (L * r) i)).eval
      (Complex.I * (θ : ℂ) / 2)‖ := by
    dsimp [a, B, t, H, complexPolynomial] at *
    exact_mod_cast hi
  have hs : ‖(complexPolynomial (U (L * r) i)).eval lambda‖ ≤ a / 2 := by
    apply (hsmall i).trans
    simpa only [a, neg_mul] using
      exp_small_of_scale B t ((D - η) * (L * r : ℕ)) hB m (k - 1) hscale
  have ht : ‖(complexDividedDifference m (U (L * r) i)).eval
      (Complex.I * (θ : ℂ) / 2)‖ ≤ Real.exp t := hT i _ hyDisk
  have hresult := small_value_forces_distance lambda (Complex.I * (θ : ℂ) / 2)
    ((complexPolynomial (U (L * r) i)).eval lambda)
    ((complexPolynomial (U (L * r) i)).eval (Complex.I * (θ : ℂ) / 2))
    ((complexDividedDifference m (U (L * r) i)).eval (Complex.I * (θ : ℂ) / 2))
    a (Real.exp t) (Real.exp_pos t)
    (complexPolynomial_eval_sub m (U (L * r) i) (hfamily.degree r hr i) _) hs hiR ht
  exact hresult

end OddPiPowers
