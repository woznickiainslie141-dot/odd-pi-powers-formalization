module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Localization.Integral

/-! A primitive integer normalization of a fraction-field polynomial divides
every integer polynomial that it divides over the fraction field. -/

@[expose] public section

namespace OddPiPowers

open Polynomial IsLocalization
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def primitiveNormalization (P : K[X]) : R[X] :=
  (integerNormalization R⁰ P).primPart

omit [IsDomain R] in
theorem primitiveNormalization_isPrimitive (P : K[X]) :
    (primitiveNormalization (R := R) P).IsPrimitive := by
  exact (integerNormalization R⁰ P).isPrimitive_primPart

theorem primitiveNormalization_map_dvd (P : K[X]) :
    (primitiveNormalization (R := R) P).map (algebraMap R K) ∣ P := by
  obtain ⟨b, hb, hbP⟩ := integerNormalization_spec R⁰ P
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := by
    intro hzero
    apply hb0
    apply (IsFractionRing.injective R K)
    simpa using hzero
  have hunit : IsUnit (C (algebraMap R K b) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbK)
  have hdiv : (primitiveNormalization (R := R) P).map (algebraMap R K) ∣
      (integerNormalization R⁰ P).map (algebraMap R K) := by
    exact Polynomial.map_dvd _ (primPart_dvd _)
  rw [hbP, Algebra.smul_def, algebraMap_apply] at hdiv
  exact hunit.dvd_mul_left.mp hdiv

/-- Gauss descent after clearing the denominators of the actual polynomial. -/
theorem primitiveNormalization_dvd_of_fraction_dvd (P : K[X]) (Q : R[X])
    (h : P ∣ Q.map (algebraMap R K)) : primitiveNormalization (R := R) P ∣ Q := by
  apply (primitiveNormalization_isPrimitive (R := R) P).dvd_of_fraction_map_dvd_fraction_map (K := K)
  exact (primitiveNormalization_map_dvd (R := R) P).trans h

theorem primitiveNormalization_eval₂_eq_zero {L : Type*} [CommRing L] [IsDomain L]
    (g : K →+* L) (hg : Function.Injective g) (P : K[X]) (hP : P ≠ 0)
    (y : L) (hy : P.eval₂ g y = 0) :
    (primitiveNormalization (R := R) P).eval₂ (g.comp (algebraMap R K)) y = 0 := by
  change (integerNormalization R⁰ P).primPart.eval₂ (g.comp (algebraMap R K)) y = 0
  apply eval₂_primPart_eq_zero (R := R) (p := integerNormalization R⁰ P)
    (f := g.comp (algebraMap R K)) (hg.comp (IsFractionRing.injective R K))
  · exact mt IsFractionRing.integerNormalization_eq_zero_iff.mp hP
  · exact integerNormalization_eval₂_eq_zero R⁰ g P hy

end OddPiPowers
