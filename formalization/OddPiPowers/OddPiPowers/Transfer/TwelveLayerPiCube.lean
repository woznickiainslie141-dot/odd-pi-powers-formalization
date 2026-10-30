module

public import OddPiPowers.Analysis.ActualReducedFamily
public import OddPiPowers.Analysis.P6NumericalRates
public import OddPiPowers.Arithmetic.P6SharpDivisorRate
public import OddPiPowers.Transfer.AuxiliaryFamilyRates
public import OddPiPowers.Transfer.IrrationalityTransfer
public import Mathlib.Tactic.NormNum

/-! The fixed P6 transfer for the actual twelve-layer integral quotient rows. -/

@[expose] public section

namespace OddPiPowers

open Filter Polynomial
open scoped Topology

/-- The coefficient polynomials use the actual positive divisor and actual
integer auxiliary family at scale `N`; this is not an abstract placeholder. -/
noncomputable def p6TwelveLayerRows : ℕ → Fin (186 + 1) → Polynomial GaussianInt :=
  actualReducedRows 186 69 (scaledTwelveLayerActualFamily 11 (by norm_num))

theorem p6TwelveLayer_actualFamily :
    AuxiliaryFamily 186 69 (651297284 / 1000000) (255596306 / 1000000)
      p6TwelveLayerRows := by
  have hA : ∀ a : Fin (186 + 1), 2 * scaledTwelveLayerOffset 11 a < 69 := by
    intro a
    have ha := scaledTwelveLayerOffset_le_eleven 11 (by norm_num) a
    omega
  have hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp (((4543599 / 100000 : ℝ) - ε) * ((69 * N : ℕ) : ℝ)) ≤
        ((scaledTwelveLayerActualFamily 11 (by norm_num) N).actualAuxiliaryPrimeDivisor : ℝ) := by
    intro ε hε
    exact PrimeRates.p6_actualDivisor_eventually_exp_lower hε
  have hfamily := actual_reduced_auxiliaryFamily 186 69 (by norm_num)
    (scaledTwelveLayerOffset 11) hA (scaledTwelveLayerActualFamily 11 (by norm_num))
    (by intro N; rfl) (by intro N a; rfl) (2113 / 20) (by norm_num)
    (4543599 / 100000) hdiv
  have hd : (651297284 / 1000000 : ℝ) ≤
      actualDecay 186 69 (scaledTwelveLayerOffset 11) (2113 / 20) + 4543599 / 100000 := by
    have h := p6_actualDecay_lower
    linarith
  have hg : actualGrowth 186 69 (scaledTwelveLayerOffset 11) - 4543599 / 100000 ≤
      (255596306 / 1000000 : ℝ) := by
    have h := p6_actualGrowth_upper
    linarith
  exact hfamily.weaken_rates hd hg

theorem pi_cube_exponentUpperBound_42170551935_div_35026168 :
    ExponentUpperBound (Real.pi ^ 3) (42170551935 / 35026168) := by
  have ht := irrationality_transfer 186 69 3 (651297284 / 1000000) (255596306 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    p6TwelveLayerRows p6TwelveLayer_actualFamily
  convert ht using 1
  norm_num

theorem pi_cube_exponentUpperBound_lt_1203973_div_1000 :
    ∃ B : ℝ, B < 1203973 / 1000 ∧ ExponentUpperBound (Real.pi ^ 3) B :=
  ⟨42170551935 / 35026168, by norm_num,
    pi_cube_exponentUpperBound_42170551935_div_35026168⟩

theorem pi_cube_not_liouvilleWith_1203973_div_1000 :
    ¬ LiouvilleWith (1203973 / 1000) (Real.pi ^ 3) :=
  not_liouvilleWith_of_exponentUpperBound
    pi_cube_exponentUpperBound_42170551935_div_35026168 (by norm_num)

end OddPiPowers
