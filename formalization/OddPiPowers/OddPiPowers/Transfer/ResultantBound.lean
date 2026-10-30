module

public import OddPiPowers.Transfer.MinimalResultant
public import OddPiPowers.Transfer.RootProduct
public import OddPiPowers.Foundations.GaussianArithmetic

/-! Quantitative lower bounds from a nonzero Gaussian resultant. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

/-- The product form is convenient for retaining exact powers before dividing.
The hypothesis on `f` splitting is automatic over `ℂ`. -/
theorem gaussian_resultant_product_bound (f U : GaussianInt[X]) (y : ℂ)
    (hf : f ≠ 0) (hroot : f.eval₂ GaussianInt.toComplex y = 0)
    (hres : resultant f U ≠ 0) (m k : ℕ)
    (hfdegree : f.natDegree ≤ k) (hUdegree : U.natDegree ≤ m)
    (B H : NNReal) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (hlead : ‖(f.leadingCoeff : ℂ)‖₊ ≤ B)
    (hbound : ∀ z ∈ (f.map GaussianInt.toComplex).roots,
      ‖(U.map GaussianInt.toComplex).eval z‖₊ ≤ H)
    (hsplit : (f.map GaussianInt.toComplex).Splits) :
    1 ≤ B ^ m * (‖(U.map GaussianInt.toComplex).eval y‖₊ * H ^ (k - 1)) := by
  let fC := f.map GaussianInt.toComplex
  let UC := U.map GaussianInt.toComplex
  have hfC : fC ≠ 0 := (Polynomial.map_ne_zero_iff GaussianInt.toComplex_injective).mpr hf
  have hy : y ∈ fC.roots := by
    apply (mem_roots hfC).mpr
    simpa only [IsRoot, fC, eval_map] using hroot
  have hcard : fC.roots.card ≤ k := by
    apply (card_roots' fC).trans
    simpa only [fC, natDegree_map_eq_of_injective GaussianInt.toComplex_injective] using hfdegree
  have hprod := root_product_bound fC.roots y hy (fun z => UC.eval z) H hH hbound k hcard
  have hformula := resultant_eq_prod_eval fC UC UC.natDegree le_rfl hsplit
  have hfdeg : fC.natDegree = f.natDegree :=
    natDegree_map_eq_of_injective GaussianInt.toComplex_injective f
  have hUdeg : UC.natDegree = U.natDegree :=
    natDegree_map_eq_of_injective GaussianInt.toComplex_injective U
  rw [hfdeg, hUdeg, resultant_map_map] at hformula
  have hres1 : (1 : NNReal) ≤ ‖((resultant f U : GaussianInt) : ℂ)‖₊ := by
    exact_mod_cast gaussian_norm_ge_one (resultant f U) hres
  have hlead' : ‖fC.leadingCoeff‖₊ ≤ B := by
    simpa only [fC, leadingCoeff_map_of_injective GaussianInt.toComplex_injective] using hlead
  have hpow : ‖fC.leadingCoeff‖₊ ^ U.natDegree ≤ B ^ m := by
    calc
      _ ≤ B ^ U.natDegree := by gcongr
      _ ≤ B ^ m := by gcongr
  calc
    1 ≤ ‖((resultant f U : GaussianInt) : ℂ)‖₊ := hres1
    _ = ‖fC.leadingCoeff‖₊ ^ U.natDegree * ‖(fC.roots.map fun z => UC.eval z).prod‖₊ := by
      rw [hformula, nnnorm_mul, nnnorm_pow]
    _ ≤ B ^ m * (‖UC.eval y‖₊ * H ^ (k - 1)) := by gcongr
    _ = _ := rfl

end OddPiPowers
