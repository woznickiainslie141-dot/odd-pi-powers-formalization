module

public import OddPiPowers.Foundations.GaussianArithmetic
public import Mathlib.RingTheory.Localization.FractionRing

/-! The Gaussian rational field and its embedding in the complex numbers. -/

@[expose] public section

namespace OddPiPowers

abbrev GaussianFraction := FractionRing GaussianInt

noncomputable def gaussianFractionEmbedding : GaussianFraction →+* ℂ :=
  IsFractionRing.lift GaussianInt.toComplex_injective

theorem gaussianFractionEmbedding_injective : Function.Injective gaussianFractionEmbedding :=
  RingHom.injective _

@[simp] theorem gaussianFractionEmbedding_algebraMap (z : GaussianInt) :
    gaussianFractionEmbedding (algebraMap GaussianInt GaussianFraction z) = (z : ℂ) := by
  exact IsFractionRing.lift_algebraMap GaussianInt.toComplex_injective z

theorem gaussianFractionEmbedding_comp :
    gaussianFractionEmbedding.comp (algebraMap GaussianInt GaussianFraction) =
      GaussianInt.toComplex := by
  apply RingHom.ext
  intro z
  exact gaussianFractionEmbedding_algebraMap z

end OddPiPowers
