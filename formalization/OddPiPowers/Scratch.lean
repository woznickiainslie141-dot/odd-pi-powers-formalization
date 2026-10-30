import OddPiPowers.Transfer.AuxiliaryFamily
import Mathlib.RingTheory.Polynomial.GaussLemma

#synth EuclideanDomain GaussianInt
#synth UniqueFactorizationMonoid GaussianInt
#synth IsGCDMonoid GaussianInt
#synth Nonempty (NormalizedGCDMonoid GaussianInt)
#check Fin.sum_univ_eq_sum_range
#check norm_sub_le
#check norm_sub_rev
#check Nat.le_mul_of_pos_left
#check Finset.single_le_sum
#check pow_lt_pow_left₀
#check Real.one_le_exp
#check Real.exp_nonneg
#check Real.exp_pos
#check NNReal.coe_le_coe
#check Real.toNNReal_of_nonneg
#check Complex.norm_real
#check norm_div
