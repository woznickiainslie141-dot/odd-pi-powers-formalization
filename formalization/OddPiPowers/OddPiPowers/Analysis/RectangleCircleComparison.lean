module

public import OddPiPowers.Analysis.RectanglePoleAlgebra
public import OddPiPowers.Analysis.RectangleLog
public import OddPiPowers.Analysis.RectangleInversePowers

/-! A rectangular Cauchy comparison for arbitrary pole order, proved by
entire divided differences and boundary primitives. -/

@[expose] public section

namespace OddPiPowers

open Complex Metric MeasureTheory

theorem real_pole_circle_ne (p : ℝ) {z : ℂ} (hz : z ∈ sphere (p : ℂ) (1 / 4)) :
    z ≠ (p : ℂ) := by
  have hh := mem_sphere.mp hz
  intro he
  rw [he, dist_self] at hh
  norm_num at hh

theorem circleIntegrable_real_pole (f : ℂ → ℂ) (hf : Continuous f) (p : ℝ) (k : ℕ) :
    CircleIntegrable (fun z => f z / (z - (p : ℂ)) ^ k) (p : ℂ) (1 / 4) := by
  apply ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1 / 4)
  apply hf.continuousOn.div ((continuous_id.sub continuous_const).pow k).continuousOn
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr (real_pole_circle_ne p hz))

theorem circleIntegral_entire_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f) (p : ℝ) :
    (∮ z in C((p : ℂ), 1 / 4), f z) = 0 := by
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (by norm_num) Set.countable_empty hf.continuous.continuousOn (fun z hz => hf z)

theorem circleIntegral_simple_real_pole (p : ℝ) :
    (∮ z in C((p : ℂ), 1 / 4), 1 / (z - (p : ℂ))) = 2 * Real.pi * Complex.I := by
  simpa only [one_div] using circleIntegral.integral_sub_center_inv (p : ℂ)
    (by norm_num : (1 / 4 : ℝ) ≠ 0)

theorem circleIntegral_higher_real_pole (p : ℝ) (j : ℕ) :
    (∮ z in C((p : ℂ), 1 / 4), 1 / (z - (p : ℂ)) ^ (j + 2)) = 0 := by
  have ht := circleIntegral.integral_sub_zpow_of_ne
    (n := -((j + 2 : ℕ) : ℤ)) (by omega) (p : ℂ) (p : ℂ) (1 / 4)
  simpa only [zpow_neg, zpow_natCast, one_div] using ht

theorem rectangleIntegral_dslope_reduce (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (p a b c d : ℝ) (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ 0) (hd : d ≠ 0) (j : ℕ) :
    rectangleIntegral (fun z => f z / (z - (p : ℂ)) ^ (j + 1)) a b c d =
      rectangleIntegral (fun z => dslope f (p : ℂ) z / (z - (p : ℂ)) ^ j) a b c d +
        f (p : ℂ) * rectangleIntegral (fun z => 1 / (z - (p : ℂ)) ^ (j + 1)) a b c d := by
  have hg := entire_dslope hf (p : ℂ)
  rw [rectangleIntegral_congr_nonpole _ _ p a b c d ha hb hc hd
    (fun z hz => pole_dslope_decomposition f (p : ℂ) j z hz)]
  rw [rectangleIntegral_add
    (rectangleIntegrable_pole _ hg.continuous p a b c d ha hb hc hd j)
    ((rectangleIntegrable_pole (fun _ : ℂ => 1) continuous_const p a b c d ha hb hc hd
      (j + 1)).const_mul (f (p : ℂ))), rectangleIntegral_const_mul]

theorem circleIntegral_dslope_reduce (f : ℂ → ℂ) (hf : Differentiable ℂ f) (p : ℝ) (j : ℕ) :
    (∮ z in C((p : ℂ), 1 / 4), f z / (z - (p : ℂ)) ^ (j + 1)) =
      (∮ z in C((p : ℂ), 1 / 4), dslope f (p : ℂ) z / (z - (p : ℂ)) ^ j) +
        f (p : ℂ) * (∮ z in C((p : ℂ), 1 / 4), 1 / (z - (p : ℂ)) ^ (j + 1)) := by
  have hg := entire_dslope hf (p : ℂ)
  have he : (∮ z in C((p : ℂ), 1 / 4), f z / (z - (p : ℂ)) ^ (j + 1)) =
      ∮ z in C((p : ℂ), 1 / 4),
        dslope f (p : ℂ) z / (z - (p : ℂ)) ^ j +
          f (p : ℂ) * (1 / (z - (p : ℂ)) ^ (j + 1)) := by
    apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1 / 4)
    intro z hz
    exact pole_dslope_decomposition f (p : ℂ) j z (real_pole_circle_ne p hz)
  rw [he, circleIntegral.integral_add (circleIntegrable_real_pole _ hg.continuous p j)]
  · rw [circleIntegral.integral_const_mul]
  · simpa only [div_eq_mul_inv, mul_one, one_mul] using
      circleIntegrable_real_pole (fun _ : ℂ => f (p : ℂ)) continuous_const p (j + 1)

/-- Full finite contour comparison for any entire numerator and pole order.
The real pole lies strictly inside the positively oriented rectangle. -/
theorem rectangleIntegral_real_pole_eq_circle (p a b c d : ℝ)
    (ha : a < p) (hb : p < b) (hc : c < 0) (hd : 0 < d)
    (j : ℕ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    rectangleIntegral (fun z => f z / (z - (p : ℂ)) ^ (j + 1)) a b c d =
      ∮ z in C((p : ℂ), 1 / 4), f z / (z - (p : ℂ)) ^ (j + 1) := by
  induction j generalizing f with
  | zero =>
    rw [rectangleIntegral_dslope_reduce f hf p a b c d ha.ne hb.ne' hc.ne hd.ne',
      circleIntegral_dslope_reduce f hf p]
    simp only [pow_zero, div_one, Nat.zero_add, pow_one]
    rw [rectangleIntegral_eq_zero_of_differentiable (entire_dslope hf (p : ℂ)),
      circleIntegral_entire_zero _ (entire_dslope hf (p : ℂ)),
      rectangleIntegral_simple_pole p a b c d ha hb hc hd, circleIntegral_simple_real_pole]
  | succ j ih =>
    rw [rectangleIntegral_dslope_reduce f hf p a b c d ha.ne hb.ne' hc.ne hd.ne',
      circleIntegral_dslope_reduce f hf p]
    rw [rectangleIntegral_higher_inverse p a b c d ha.ne hb.ne' hc.ne hd.ne' j,
      circleIntegral_higher_real_pole p j]
    simp only [mul_zero, add_zero]
    exact ih (dslope f (p : ℂ)) (entire_dslope hf (p : ℂ))

end OddPiPowers
