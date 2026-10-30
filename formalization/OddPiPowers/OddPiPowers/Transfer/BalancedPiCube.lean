module

public import OddPiPowers.Analysis.BalancedAuxiliaryFamily
public import OddPiPowers.Analysis.BalancedNumericCertificate
public import OddPiPowers.Transfer.AuxiliaryFamilyRates
public import OddPiPowers.Transfer.IrrationalityTransfer

/-! A first unconditional numeric pi^3 instance, before the sharper P6 target. -/

@[expose] public section

namespace OddPiPowers

theorem balanced_512_actualFamily :
    AuxiliaryFamily 511 1 2000 900 (balancedGaussianRows 511) := by
  have hd : (2000 : ℝ) ≤ balancedDecay 511 128 := by
    simpa [balancedDecay, balancedD0] using balancedD0_lower
  have hg : balancedGrowth 511 ≤ 900 := by
    simpa [balancedGrowth, balancedG0] using balancedG0_upper
  exact (balanced_actual_auxiliaryFamily 511 128 (by norm_num)).weaken_rates hd hg

theorem pi_cube_exponentUpperBound_14819_div_two :
    ExponentUpperBound (Real.pi ^ 3) (14819 / 2) := by
  have ht := irrationality_transfer 511 1 3 2000 900
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (balancedGaussianRows 511) balanced_512_actualFamily
  convert ht using 1
  norm_num

theorem pi_cube_exponentUpperBound_lt_7500 :
    ∃ B : ℝ, B < 7500 ∧ ExponentUpperBound (Real.pi ^ 3) B :=
  ⟨14819 / 2, by norm_num, pi_cube_exponentUpperBound_14819_div_two⟩

theorem pi_cube_not_liouvilleWith_7500 : ¬ LiouvilleWith 7500 (Real.pi ^ 3) :=
  not_liouvilleWith_of_exponentUpperBound pi_cube_exponentUpperBound_14819_div_two (by norm_num)

end OddPiPowers
