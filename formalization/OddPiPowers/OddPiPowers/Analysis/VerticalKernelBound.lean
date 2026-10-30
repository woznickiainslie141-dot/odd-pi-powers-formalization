module

public import OddPiPowers.Analysis.ActualPartialFractions
public import OddPiPowers.Analysis.ActualHorizontalGeometry
public import Mathlib.Topology.Algebra.Polynomial

/-! Uniform rational bounds on a finite vertical segment. Scale n is fixed
when the real coordinate tends to infinity. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem denominatorValue_norm_product (z : ℂ) :
    ‖P.denominatorValue z‖ = ∏ a : Fin M, ∏ r ∈ P.interval a, ‖z + (r : ℂ)‖ := by
  classical
  simp only [denominatorValue, denominator, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.C_eq_natCast,
    Polynomial.eval₂_natCast, norm_prod]

theorem vertical_pole_factor_lower (R : ℝ) (_hR : 0 ≤ R) (hn : 2 * (P.n : ℝ) ≤ R)
    (z : ℂ) (hz : |z.re| = R) (r : ℕ) (hr : r ≤ P.n) :
    R / 2 ≤ ‖z + (r : ℂ)‖ := by
  have hrR : (r : ℝ) ≤ R / 2 := by
    have hrn : (r : ℝ) ≤ P.n := by exact_mod_cast hr
    linarith
  have h := abs_sub_abs_le_abs_sub z.re (-(r : ℝ))
  simp only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity),
    sub_neg_eq_add, hz] at h
  have ha := Complex.abs_re_le_norm (z + (r : ℂ))
  simp only [Complex.add_re, Complex.natCast_re] at ha
  linarith

theorem vertical_denominator_lower (R : ℝ) (hR : 0 ≤ R)
    (hn : 2 * (P.n : ℝ) ≤ R) (z : ℂ) (hz : |z.re| = R) :
    (R / 2) ^ P.denominator.natDegree ≤ ‖P.denominatorValue z‖ := by
  classical
  rw [P.denominator_natDegree, P.totalMultiplicity_eq_sum_interval_card,
    P.denominatorValue_norm_product, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun a ha => pow_nonneg (by positivity) _)
  intro a ha
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun r hr => by positivity)
  intro r hr
  exact P.vertical_pole_factor_lower R hR hn z hz r
    (((P.interval_mem_iff a r).mp hr).2.trans (P.right_le_n a))

theorem vertical_rationalKernel_bound (R : ℝ) (hR : 2 ≤ R)
    (hn : 2 * (P.n : ℝ) ≤ R) (z : ℂ) (hre : |z.re| = R) (him : |z.im| ≤ R)
    (h : ℕ) (hd : h + 2 ≤ P.denominator.natDegree) :
    ‖z ^ h / P.denominatorValue z‖ ≤
      ((2 : ℝ) ^ h * 2 ^ (h + 2)) / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hhalf : 0 < R / 2 := by positivity
  have hQ := P.vertical_denominator_lower R hR0.le hn z hre
  have hpow : (R / 2) ^ (h + 2) ≤ (R / 2) ^ P.denominator.natDegree :=
    pow_le_pow_right₀ (by linarith) hd
  have hden := hpow.trans hQ
  have hQpos : 0 < ‖P.denominatorValue z‖ := (pow_pos hhalf _).trans_le hden
  have hz : ‖z‖ ≤ 2 * R := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [hre] at hh
    linarith
  calc
    _ = ‖z‖ ^ h / ‖P.denominatorValue z‖ := by rw [norm_div, norm_pow]
    _ ≤ (2 * R) ^ h / ‖P.denominatorValue z‖ :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz h) hQpos.le
    _ ≤ (2 * R) ^ h / (R / 2) ^ (h + 2) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hhalf _) hden
    _ = _ := by
      rw [mul_pow, div_pow, pow_add R h 2]
      field_simp

theorem continuous_denominatorValue : Continuous P.denominatorValue :=
  P.denominator.continuous_eval₂ (Rat.castHom ℂ)

end OddPiPowers.ActualIntervals
