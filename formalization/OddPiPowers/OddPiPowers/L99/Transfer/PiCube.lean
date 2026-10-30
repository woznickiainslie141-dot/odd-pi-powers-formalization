module
public import OddPiPowers.Analysis.ActualReducedFamily
public import OddPiPowers.L99.Analysis.L99NumericalRates
public import OddPiPowers.L99.Arithmetic.L99SharpDivisorRate
public import OddPiPowers.Transfer.AuxiliaryFamilyRates
public import OddPiPowers.Transfer.IrrationalityTransfer
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace OddPiPowers.L99
open Filter Polynomial
open scoped Topology

noncomputable def l99Rows : ℕ → Fin (171 + 1) → Polynomial GaussianInt :=
  actualReducedRows 171 99 (scaledTwentyEightLayerActualFamily 4 (by norm_num))

theorem l99_actualFamily : AuxiliaryFamily 171 99 (54469491 / 100000) (2672657 / 12500) l99Rows := by
  have hA : ∀ a : Fin (171 + 1), 2 * scaledTwentyEightLayerOffset 4 a < 99 := by
    intro a
    have ha := scaledTwentyEightLayerOffset_le_twentySeven 4 (by norm_num) a
    omega
  have hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp (((2761813 / 50000) - ε) * ((99 * N : ℕ) : ℝ)) ≤
        ((scaledTwentyEightLayerActualFamily 4 (by norm_num) N).actualAuxiliaryPrimeDivisor : ℝ) := by
    intro ε hε
    exact PrimeRates.l99_actualDivisor_eventually_exp_lower hε
  have hfamily := actual_reduced_auxiliaryFamily 171 99 (by norm_num)
    (scaledTwentyEightLayerOffset 4) hA (scaledTwentyEightLayerActualFamily 4 (by norm_num))
    (by intro N; rfl) (by intro N a; rfl) (1801 / 20) (by norm_num) (2761813 / 50000) hdiv
  have hd : ((54469491 / 100000) : ℝ) ≤ actualDecay 171 99 (scaledTwentyEightLayerOffset 4) (1801 / 20) + (2761813 / 50000) := by
    have h := l99_actualDecay_lower
    linarith
  have hg : actualGrowth 171 99 (scaledTwentyEightLayerOffset 4) - (2761813 / 50000) ≤ ((2672657 / 12500) : ℝ) := by
    have h := l99_actualGrowth_upper
    linarith
  exact hfamily.weaken_rates hd hg

theorem pi_cube_exponentUpperBound_l99_exact :
    ExponentUpperBound (Real.pi ^ 3) (12970477737 / 11706979) := by
  have ht := irrationality_transfer 171 99 3 (54469491 / 100000) (2672657 / 12500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    l99Rows l99_actualFamily
  convert ht using 1
  norm_num

theorem pi_cube_exponentUpperBound_lt_110793_div_100 :
    ∃ B : ℝ, B < 110793 / 100 ∧ ExponentUpperBound (Real.pi ^ 3) B :=
  ⟨(12970477737 / 11706979), by norm_num, pi_cube_exponentUpperBound_l99_exact⟩

theorem pi_cube_not_liouvilleWith_110793_div_100 :
    ¬ LiouvilleWith (110793 / 100) (Real.pi ^ 3) :=
  not_liouvilleWith_of_exponentUpperBound pi_cube_exponentUpperBound_l99_exact (by norm_num)

end OddPiPowers.L99
