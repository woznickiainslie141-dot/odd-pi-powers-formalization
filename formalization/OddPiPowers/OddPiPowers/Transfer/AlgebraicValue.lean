module

public import OddPiPowers.Foundations.GaussianFraction
public import OddPiPowers.Transfer.ResultantBound
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! A value bound using the primitive minimal polynomial of the chosen point. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

noncomputable local instance : Algebra GaussianFraction ℂ :=
  gaussianFractionEmbedding.toAlgebra

noncomputable local instance : NormalizedGCDMonoid GaussianInt :=
  Classical.choice inferInstance

/-- The annihilating polynomial controls the degree and leading coefficient;
nonvanishing comes from the actual minimal polynomial. All roots of the
annihilator are required to lie in the disk on which `U` is bounded. -/
theorem gaussian_algebraic_value_product_bound
    (F U : GaussianInt[X]) (y : ℂ) (hF : F ≠ 0)
    (hFroot : F.eval₂ GaussianInt.toComplex y = 0)
    (hU : U.eval₂ GaussianInt.toComplex y ≠ 0)
    (m k : ℕ) (hFdegree : F.natDegree ≤ k) (hUdegree : U.natDegree ≤ m)
    (B H : NNReal) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (hFlead : ‖(F.leadingCoeff : ℂ)‖₊ ≤ B)
    (hroots : ∀ z : ℂ, F.eval₂ GaussianInt.toComplex z = 0 → ‖z‖ ≤ 2)
    (hheight : ∀ z : ℂ, ‖z‖ ≤ 2 → ‖(U.map GaussianInt.toComplex).eval z‖₊ ≤ H) :
    1 ≤ B ^ m * (‖(U.map GaussianInt.toComplex).eval y‖₊ * H ^ (k - 1)) := by
  have hcomp : (algebraMap GaussianFraction ℂ).comp
      (algebraMap GaussianInt GaussianFraction) = GaussianInt.toComplex := by
    exact gaussianFractionEmbedding_comp
  have hFmap : (F.map (algebraMap GaussianInt GaussianFraction)).aeval y = 0 := by
    rw [aeval_def, eval₂_map, hcomp]
    exact hFroot
  have hy : IsIntegral GaussianFraction y := by
    apply IsAlgebraic.isIntegral
    exact ⟨F.map (algebraMap GaussianInt GaussianFraction),
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective _ _)).mpr hF, hFmap⟩
  let f := primitiveNormalization (R := GaussianInt) (minpoly GaussianFraction y)
  have hf : f ≠ 0 := (primitiveNormalization_isPrimitive (R := GaussianInt)
    (minpoly GaussianFraction y)).ne_zero
  have hfdvd : f ∣ F := by
    apply primitive_minpoly_dvd y F
    simpa only [hcomp] using hFroot
  have hfroot : f.eval₂ GaussianInt.toComplex y = 0 := by
    simpa only [hcomp] using primitive_minpoly_eval₂_eq_zero (R := GaussianInt) y hy
  have hres : resultant f U ≠ 0 := by
    apply primitive_minpoly_resultant_ne_zero y hy U
    simpa only [hcomp] using hU
  have hfdegree : f.natDegree ≤ k := (natDegree_le_of_dvd hfdvd hF).trans hFdegree
  have hlead : ‖(f.leadingCoeff : ℂ)‖₊ ≤ B :=
    (gaussian_nnnorm_le_of_dvd (leadingCoeff_ne_zero.mpr hF)
      (leadingCoeff_dvd_leadingCoeff hfdvd)).trans hFlead
  have hbound : ∀ z ∈ (f.map GaussianInt.toComplex).roots,
      ‖(U.map GaussianInt.toComplex).eval z‖₊ ≤ H := by
    intro z hz
    have hfmapne : f.map GaussianInt.toComplex ≠ 0 :=
      (Polynomial.map_ne_zero_iff GaussianInt.toComplex_injective).mpr hf
    have hfz : f.eval₂ GaussianInt.toComplex z = 0 := by
      have hz' := (mem_roots hfmapne).mp hz
      simpa only [IsRoot, eval_map] using hz'
    have hFz : F.eval₂ GaussianInt.toComplex z = 0 := by
      obtain ⟨Q, hQ⟩ := hfdvd
      rw [hQ, eval₂_mul, hfz, zero_mul]
    exact hheight z (hroots z hFz)
  exact gaussian_resultant_product_bound f U y hf hfroot hres m k hfdegree hUdegree
    B H hB hH hlead hbound (IsAlgClosed.splits _)

/-- Reciprocal form of the algebraic-value estimate. -/
theorem gaussian_algebraic_value_lower_bound
    (F U : GaussianInt[X]) (y : ℂ) (hF : F ≠ 0)
    (hFroot : F.eval₂ GaussianInt.toComplex y = 0)
    (hU : U.eval₂ GaussianInt.toComplex y ≠ 0)
    (m k : ℕ) (hFdegree : F.natDegree ≤ k) (hUdegree : U.natDegree ≤ m)
    (B H : NNReal) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (hFlead : ‖(F.leadingCoeff : ℂ)‖₊ ≤ B)
    (hroots : ∀ z : ℂ, F.eval₂ GaussianInt.toComplex z = 0 → ‖z‖ ≤ 2)
    (hheight : ∀ z : ℂ, ‖z‖ ≤ 2 → ‖(U.map GaussianInt.toComplex).eval z‖₊ ≤ H) :
    1 / (B ^ m * H ^ (k - 1)) ≤ ‖(U.map GaussianInt.toComplex).eval y‖₊ := by
  apply inverse_product_le_of_one_le_mul (B ^ m) (H ^ (k - 1))
    ‖(U.map GaussianInt.toComplex).eval y‖₊
    (pow_pos (zero_lt_one.trans_le hB) _) (pow_pos (zero_lt_one.trans_le hH) _)
  exact gaussian_algebraic_value_product_bound F U y hF hFroot hU m k hFdegree hUdegree
    B H hB hH hFlead hroots hheight

end OddPiPowers
