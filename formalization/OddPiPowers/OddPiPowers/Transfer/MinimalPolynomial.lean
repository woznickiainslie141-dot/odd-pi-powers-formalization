module

public import OddPiPowers.Transfer.PrimitiveNormalization
public import Mathlib.FieldTheory.Minpoly.Field

/-! Primitive minimal polynomials over an integral domain and its fraction field. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

variable {R K L : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L]

/-- The primitive normalization of the actual minimal polynomial still
vanishes at the chosen algebraic point. -/
theorem primitive_minpoly_eval₂_eq_zero (y : L) (hy : IsIntegral K y) :
    (primitiveNormalization (R := R) (minpoly K y)).eval₂
      ((algebraMap K L).comp (algebraMap R K)) y = 0 := by
  apply primitiveNormalization_eval₂_eq_zero (algebraMap K L) (RingHom.injective _)
    (minpoly K y) (minpoly.ne_zero hy)
  simpa only [aeval_def] using minpoly.aeval K y

/-- It divides every integral-coefficient annihilating polynomial. -/
theorem primitive_minpoly_dvd (y : L) (F : R[X])
    (hF : F.eval₂ ((algebraMap K L).comp (algebraMap R K)) y = 0) :
    primitiveNormalization (R := R) (minpoly K y) ∣ F := by
  apply primitiveNormalization_dvd_of_fraction_dvd
  apply minpoly.dvd K y
  simpa only [aeval_def, eval₂_map] using hF

/-- Its image in the fraction field is associated to the monic minimal
polynomial. This is the bridge needed for irreducibility and root counting. -/
theorem primitive_minpoly_associated (y : L) (hy : IsIntegral K y) :
    Associated (minpoly K y)
      ((primitiveNormalization (R := R) (minpoly K y)).map (algebraMap R K)) := by
  apply associated_of_dvd_dvd
  · apply minpoly.dvd K y
    simpa only [aeval_def, eval₂_map] using primitive_minpoly_eval₂_eq_zero (R := R) y hy
  · exact primitiveNormalization_map_dvd (R := R) (minpoly K y)

theorem primitive_minpoly_irreducible_map (y : L) (hy : IsIntegral K y) :
    Irreducible ((primitiveNormalization (R := R) (minpoly K y)).map (algebraMap R K)) :=
  (primitive_minpoly_associated (R := R) y hy).irreducible (minpoly.irreducible hy)

end OddPiPowers
