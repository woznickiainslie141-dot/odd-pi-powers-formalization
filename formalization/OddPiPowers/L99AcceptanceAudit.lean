module
public import OddPiPowers.L99.Transfer.PiCube

example : OddPiPowers.ExponentUpperBound (Real.pi ^ 3) (12970477737 / 11706979) :=
  OddPiPowers.L99.pi_cube_exponentUpperBound_l99_exact

example : ∃ B : ℝ, B < 110793 / 100 ∧ OddPiPowers.ExponentUpperBound (Real.pi ^ 3) B :=
  OddPiPowers.L99.pi_cube_exponentUpperBound_lt_110793_div_100

example : ¬ LiouvilleWith (110793 / 100) (Real.pi ^ 3) :=
  OddPiPowers.L99.pi_cube_not_liouvilleWith_110793_div_100

example : OddPiPowers.AuxiliaryFamily 171 99 (54469491 / 100000) (2672657 / 12500)
    OddPiPowers.L99.l99Rows := OddPiPowers.L99.l99_actualFamily

#print axioms OddPiPowers.L99.twentyEightLayerCellTable_all_valid
#print axioms OddPiPowers.L99.twentyEightLayerCellTable_pairwise_disjoint
#print axioms OddPiPowers.L99.twentyEightLayerLowerBound_le_cost
#print axioms OddPiPowers.L99.scaledTwentyEightLayerActualGrouping
#print axioms OddPiPowers.L99.scaledTwentyEightLayer_shapeRelativeLength
#print axioms OddPiPowers.L99.l99_actualDecay_lower
#print axioms OddPiPowers.L99.l99_actualGrowth_upper
#print axioms OddPiPowers.L99.PrimeRates.l99_prefix_floor_lower
#print axioms OddPiPowers.L99.PrimeRates.l99_tail_floor_lower
#print axioms OddPiPowers.L99.PrimeRates.l99_finite_window_rate_lower
#print axioms OddPiPowers.L99.PrimeRates.l99_actualDivisor_eventually_exp_lower
#print axioms OddPiPowers.L99.l99_actualFamily
#print axioms OddPiPowers.L99.pi_cube_exponentUpperBound_l99_exact
#print axioms OddPiPowers.L99.pi_cube_exponentUpperBound_lt_110793_div_100
#print axioms OddPiPowers.L99.pi_cube_not_liouvilleWith_110793_div_100
