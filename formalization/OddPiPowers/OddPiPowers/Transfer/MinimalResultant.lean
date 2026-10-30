module

public import OddPiPowers.Transfer.MinimalPolynomial
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Nonvanishing uses the actual minimal polynomial, not an arbitrary
annihilating polynomial which may have other common roots with `U`. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

variable {R K L : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L]

/-- A polynomial nonzero at the selected algebraic point has nonzero
resultant with the primitive normalization of that point's minimal polynomial. -/
theorem primitive_minpoly_resultant_ne_zero (y : L) (hy : IsIntegral K y) (U : R[X])
    (hU : U.eval₂ ((algebraMap K L).comp (algebraMap R K)) y ≠ 0) :
    resultant (primitiveNormalization (R := R) (minpoly K y)) U ≠ 0 := by
  let f := primitiveNormalization (R := R) (minpoly K y)
  have hfroot : f.eval₂ ((algebraMap K L).comp (algebraMap R K)) y = 0 :=
    primitive_minpoly_eval₂_eq_zero (R := R) y hy
  have hnotdvd : ¬f.map (algebraMap R K) ∣ U.map (algebraMap R K) := by
    intro hdiv
    obtain ⟨Q, hQ⟩ := hdiv
    apply hU
    rw [← eval₂_map, hQ, eval₂_mul, eval₂_map, hfroot, zero_mul]
  have hcop : IsCoprime (f.map (algebraMap R K)) (U.map (algebraMap R K)) :=
    (primitive_minpoly_irreducible_map (R := R) y hy).coprime_iff_not_dvd.mpr hnotdvd
  have hres := resultant_ne_zero (f.map (algebraMap R K)) (U.map (algebraMap R K)) hcop
  have hmap : (algebraMap R K) (resultant f U) ≠ 0 := by
    simpa only [natDegree_map_eq_of_injective (IsFractionRing.injective R K),
      resultant_map_map] using hres
  intro hzero
  apply hmap
  rw [hzero, map_zero]

end OddPiPowers
