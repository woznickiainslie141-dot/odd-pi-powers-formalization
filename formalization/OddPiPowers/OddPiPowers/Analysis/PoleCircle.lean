module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Disjoint small circles about integer poles and exact Cauchy integrals.
The fixed radius is 1/4; no general residue theorem is assumed. -/

@[expose] public section

namespace OddPiPowers

open Complex Metric

theorem integer_pole_norm_gap (r pole : ℕ) (hne : r ≠ pole) :
    1 ≤ ‖(r : ℂ) - (pole : ℂ)‖ := by
  have hnorm : ‖(r : ℂ) - (pole : ℂ)‖ = |(r : ℝ) - (pole : ℝ)| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  rcases lt_or_gt_of_ne hne with h | h
  · have hr : (r : ℝ) + 1 ≤ pole := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hr : (pole : ℝ) + 1 ≤ r := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem integer_pole_closedBalls_disjoint (r pole : ℕ) (hne : r ≠ pole) :
    Disjoint (closedBall (-(r : ℂ)) (1 / 4)) (closedBall (-(pole : ℂ)) (1 / 4)) := by
  apply Set.disjoint_left.mpr
  intro z hz hr
  have hz' := mem_closedBall.mp hz
  have hr' := mem_closedBall.mp hr
  rw [dist_comm] at hz'
  have ht := dist_triangle (-(r : ℂ)) z (-(pole : ℂ))
  have hg : 1 ≤ dist (-(r : ℂ)) (-(pole : ℂ)) := by
    rw [dist_eq_norm]
    have heq : -(r : ℂ) - -(pole : ℂ) = -((r : ℂ) - (pole : ℂ)) := by ring
    rw [heq, norm_neg]
    exact integer_pole_norm_gap r pole hne
  linarith

theorem pole_factor_ne_zero_on_other_closedBall (r pole : ℕ) (hne : r ≠ pole)
    {z : ℂ} (hz : z ∈ closedBall (-(pole : ℂ)) (1 / 4)) : z + (r : ℂ) ≠ 0 := by
  intro he
  have hez : z = -(r : ℂ) := eq_neg_of_add_eq_zero_left he
  rw [hez] at hz
  have hd := mem_closedBall.mp hz
  rw [dist_eq_norm] at hd
  have heq : -(r : ℂ) - -(pole : ℂ) = -((r : ℂ) - (pole : ℂ)) := by ring
  rw [heq, norm_neg] at hd
  have hg := integer_pole_norm_gap r pole hne
  linarith

theorem pole_factor_ne_zero_on_own_sphere (pole : ℕ) {z : ℂ}
    (hz : z ∈ sphere (-(pole : ℂ)) (1 / 4)) : z + (pole : ℂ) ≠ 0 := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm, sub_neg_eq_add] at hd
  exact norm_ne_zero_iff.mp (by rw [hd]; norm_num)

theorem all_pole_factors_ne_zero_on_sphere (pole r : ℕ) {z : ℂ}
    (hz : z ∈ sphere (-(pole : ℂ)) (1 / 4)) : z + (r : ℂ) ≠ 0 := by
  by_cases he : r = pole
  · subst r
    exact pole_factor_ne_zero_on_own_sphere pole hz
  · exact pole_factor_ne_zero_on_other_closedBall r pole he (sphere_subset_closedBall hz)

theorem poleTerm_circleIntegrable (f : ℂ → ℂ) (hf : Continuous f)
    (pole r j : ℕ) :
    CircleIntegrable (fun z => f z / (z + (r : ℂ)) ^ (j + 1)) (-(pole : ℂ)) (1 / 4) := by
  apply ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1 / 4)
  apply hf.continuousOn.div ((continuous_id.add continuous_const).pow _).continuousOn
  intro z hz
  exact pow_ne_zero _ (all_pole_factors_ne_zero_on_sphere pole r hz)

theorem poleTerm_circleIntegral_center (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (pole j : ℕ) :
    (∮ z in C(-(pole : ℂ), 1 / 4), f z / (z + (pole : ℂ)) ^ (j + 1)) =
      (2 * Real.pi * Complex.I / (Nat.factorial j : ℂ)) *
        iteratedDeriv j f (-(pole : ℂ)) := by
  have h := hf.differentiableOn.circleIntegral_one_div_sub_center_pow_smul
    (c := -(pole : ℂ)) (R := 1 / 4) (by norm_num) j
  simpa only [smul_eq_mul, sub_neg_eq_add, one_div, div_eq_mul_inv, one_mul, mul_comm] using h

theorem poleTerm_circleIntegral_other (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (pole r j : ℕ) (hne : r ≠ pole) :
    (∮ z in C(-(pole : ℂ), 1 / 4), f z / (z + (r : ℂ)) ^ (j + 1)) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (by norm_num : (0 : ℝ) ≤ 1 / 4) Set.countable_empty
  · apply hf.continuous.continuousOn.div
      ((continuous_id.add continuous_const).pow _).continuousOn
    intro z hz
    exact pow_ne_zero _ (pole_factor_ne_zero_on_other_closedBall r pole hne hz)
  · intro z hz
    exact (hf z).div
      ((differentiableAt_id.add_const (r : ℂ)).pow _)
      (pow_ne_zero _ (pole_factor_ne_zero_on_other_closedBall r pole hne
        (ball_subset_closedBall hz.1)))

end OddPiPowers
