module

public import OddPiPowers.Transfer.Binomial

/-! The binomial attached to a rational approximation to a power of π. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

noncomputable def rationalPowerBinomial (p : ℤ) (q k : ℕ) : GaussianInt[X] :=
  gaussianBinomial (((2 ^ k * q : ℕ) : GaussianInt)) (gaussianI ^ k * (p : GaussianInt)) k

theorem rationalPowerBinomial_root (p : ℤ) (q k : ℕ) (hq : 0 < q)
    (θ : ℝ) (hθ : θ ^ k = (p : ℝ) / q) :
    (rationalPowerBinomial p q k).eval₂ GaussianInt.toComplex
      (Complex.I * (θ : ℂ) / 2) = 0 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hθC : (θ : ℂ) ^ k = (p : ℂ) / q := by exact_mod_cast hθ
  simp only [rationalPowerBinomial, gaussianBinomial, eval₂_sub, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X]
  simp only [map_mul, map_pow, map_natCast, map_intCast, map_ofNat,
    gaussianI_toComplex, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, div_pow, hθC]
  field_simp
  simp

/-- Uniform algebraic lower bound for any numerator and positive denominator,
including unreduced fractions and reducible binomials. -/
theorem rational_power_value_lower_bound (p : ℤ) (q k : ℕ) (hq : 0 < q) (hk : 0 < k)
    (θ : ℝ) (hθ : θ ^ k = (p : ℝ) / q)
    (hyDisk : ‖Complex.I * (θ : ℂ) / 2‖ ≤ 2)
    (U : GaussianInt[X])
    (hU : U.eval₂ GaussianInt.toComplex (Complex.I * (θ : ℂ) / 2) ≠ 0)
    (m : ℕ) (hUdegree : U.natDegree ≤ m) (H : NNReal) (hH : 1 ≤ H)
    (hheight : ∀ z : ℂ, ‖z‖ ≤ 2 → ‖(U.map GaussianInt.toComplex).eval z‖₊ ≤ H) :
    1 / (((2 : NNReal) ^ k * q) ^ m * H ^ (k - 1)) ≤
      ‖(U.map GaussianInt.toComplex).eval (Complex.I * (θ : ℂ) / 2)‖₊ := by
  let a : GaussianInt := ((2 ^ k * q : ℕ) : GaussianInt)
  let b : GaussianInt := gaussianI ^ k * (p : GaussianInt)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (Nat.mul_ne_zero (pow_ne_zero k (by decide : (2 : ℕ) ≠ 0)) (Nat.ne_of_gt hq))
  have hB : (1 : NNReal) ≤ (2 : NNReal) ^ k * q := by
    have htwo : (1 : NNReal) ≤ (2 : NNReal) ^ k := one_le_pow₀ (by norm_num)
    have hq' : (1 : NNReal) ≤ q := by exact_mod_cast hq
    calc
      1 = (1 : NNReal) * 1 := by norm_num
      _ ≤ (2 : NNReal) ^ k * q := mul_le_mul' htwo hq'
  have haB : ‖(a : ℂ)‖₊ ≤ (2 : NNReal) ^ k * q := by
    have htwo : GaussianInt.toComplex 2 = (2 : ℂ) := by
      simpa only [Nat.cast_ofNat] using (map_natCast GaussianInt.toComplex 2)
    simp [a, htwo]
  have hy : (gaussianBinomial a b k).eval₂ GaussianInt.toComplex
      (Complex.I * (θ : ℂ) / 2) = 0 := by
    exact rationalPowerBinomial_root p q k hq θ hθ
  exact gaussian_binomial_value_lower_bound a b k ha hk _ hy hyDisk U hU m hUdegree
    ((2 : NNReal) ^ k * q) H hB hH haB hheight

end OddPiPowers
