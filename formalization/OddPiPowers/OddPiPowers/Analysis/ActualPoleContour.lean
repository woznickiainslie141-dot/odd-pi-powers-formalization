module

public import OddPiPowers.Analysis.ActualPartialFractions
public import OddPiPowers.Analysis.PoleCircle
public import OddPiPowers.Analysis.ContourExponential
public import OddPiPowers.Analysis.ActualRemainderAlgebra

/-! A genuine finite contour representation of the actual remainder.
The contour is the sum of disjoint positively oriented radius-1/4 circles. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

open Complex Metric

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def meromorphicExponentialKernel (h : ℕ) (lambda z : ℂ) : ℂ :=
  P.factorialRationalKernel h z * contourExponential lambda P.n z

noncomputable def principalExponentialTerm (h : ℕ) (lambda : ℂ) (r q : ℕ) (z : ℂ) : ℂ :=
  ((PowerSeries.coeff q (P.localExpansion r h) : ℚ) : ℂ) *
    (contourExponential lambda P.n z / (z + (r : ℂ)) ^ (P.multiplicity r - q))

theorem meromorphicExponentialKernel_principalSum (h : Fin M) (hM : 0 < M)
    (lambda z : ℂ) (hz : ∀ r : ℕ, r ≤ P.n → z + (r : ℂ) ≠ 0) :
    P.meromorphicExponentialKernel h.val lambda z =
      ∑ r ∈ Finset.range (P.n + 1), ∑ q ∈ Finset.range (P.multiplicity r),
        P.principalExponentialTerm h.val lambda r q z := by
  rw [meromorphicExponentialKernel, P.factorialRationalKernel_partialFractions h hM z hz]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  unfold principalExponentialTerm
  ring

set_option backward.isDefEq.respectTransparency false in
theorem principalExponentialTerm_circleIntegrable (h : ℕ) (lambda : ℂ)
    (pole r q : ℕ) (hq : q < P.multiplicity r) :
    CircleIntegrable (P.principalExponentialTerm h lambda r q) (-(pole : ℂ)) (1 / 4) := by
  have he : P.multiplicity r - q = (P.multiplicity r - 1 - q) + 1 := by omega
  have hi := poleTerm_circleIntegrable (contourExponential lambda P.n)
    (contourExponential_continuous lambda P.n) pole r (P.multiplicity r - 1 - q)
  unfold principalExponentialTerm
  rw [he]
  exact IntervalIntegrable.const_mul hi
    (((PowerSeries.coeff q (P.localExpansion r h) : ℚ) : ℂ))

theorem principalExponentialTerm_circleIntegral (h : ℕ) (lambda : ℂ)
    (pole r q : ℕ) (hq : q < P.multiplicity r) :
    (∮ z in C(-(pole : ℂ), 1 / 4), P.principalExponentialTerm h lambda r q z) =
      if r = pole then
        (2 * Real.pi * Complex.I) *
          (((PowerSeries.coeff q (P.localExpansion r h) : ℚ) : ℂ) *
            contourExponential lambda P.n (-(r : ℂ)) *
              lambda ^ (P.multiplicity r - 1 - q) /
                (Nat.factorial (P.multiplicity r - 1 - q) : ℂ))
      else 0 := by
  have he : P.multiplicity r - q = (P.multiplicity r - 1 - q) + 1 := by omega
  simp only [principalExponentialTerm, he, circleIntegral.integral_const_mul]
  by_cases hr : r = pole
  · subst r
    rw [ite_eq_left rfl, poleTerm_circleIntegral_center _
      (contourExponential_differentiable lambda P.n), iteratedDeriv_contourExponential]
    ring
  · rw [ite_eq_right hr, poleTerm_circleIntegral_other _
      (contourExponential_differentiable lambda P.n) _ _ _ hr, mul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem meromorphicExponentialKernel_circleIntegral (h : Fin M) (hM : 0 < M)
    (lambda : ℂ) (pole : ℕ) (hpole : pole ≤ P.n) :
    (∮ z in C(-(pole : ℂ), 1 / 4), P.meromorphicExponentialKernel h.val lambda z) =
      (2 * Real.pi * Complex.I) *
        ∑ q ∈ Finset.range (P.multiplicity pole),
          (((PowerSeries.coeff q (P.localExpansion pole h.val) : ℚ) : ℂ) *
            contourExponential lambda P.n (-(pole : ℂ)) *
              lambda ^ (P.multiplicity pole - 1 - q) /
                (Nat.factorial (P.multiplicity pole - 1 - q) : ℂ)) := by
  classical
  have hc : (∮ z in C(-(pole : ℂ), 1 / 4), P.meromorphicExponentialKernel h.val lambda z) =
      ∮ z in C(-(pole : ℂ), 1 / 4),
        ∑ r ∈ Finset.range (P.n + 1), ∑ q ∈ Finset.range (P.multiplicity r),
          P.principalExponentialTerm h.val lambda r q z := by
    apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1 / 4)
    intro z hz
    exact P.meromorphicExponentialKernel_principalSum h hM lambda z
      (fun r hr => all_pole_factors_ne_zero_on_sphere pole r hz)
  rw [hc, circleIntegral.integral_fun_sum]
  · simp_rw [circleIntegral.integral_fun_sum (fun q hq =>
      P.principalExponentialTerm_circleIntegrable h.val lambda pole _ q (Finset.mem_range.mp hq))]
    have hp : pole ∈ Finset.range (P.n + 1) := by simp [hpole]
    rw [Finset.sum_eq_single_of_mem pole hp]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [P.principalExponentialTerm_circleIntegral h.val lambda pole pole q
        (Finset.mem_range.mp hq), ite_eq_left rfl]
    · intro r hr hne
      apply Finset.sum_eq_zero
      intro q hq
      rw [P.principalExponentialTerm_circleIntegral h.val lambda pole r q
        (Finset.mem_range.mp hq), ite_eq_right hne]
  · intro r hr
    exact CircleIntegrable.fun_sum _ (fun q hq =>
      P.principalExponentialTerm_circleIntegrable h.val lambda pole r q (Finset.mem_range.mp hq))

noncomputable def finitePoleContour (h : ℕ) (lambda : ℂ) : ℂ :=
  ∑ pole ∈ Finset.range (P.n + 1),
    ∮ z in C(-(pole : ℂ), 1 / 4), P.meromorphicExponentialKernel h lambda z

theorem finitePoleContour_eq_derivativeSum (h : Fin M) (hM : 0 < M) (lambda : ℂ) :
    P.finitePoleContour h.val lambda = (2 * Real.pi * Complex.I) *
      ∑ pole ∈ Finset.range (P.n + 1), ∑ j : Fin M,
        ((P.localCoefficient pole h.val j.val : ℚ) : ℂ) *
          (contourExponential lambda P.n (-(pole : ℂ)) * lambda ^ j.val /
            (Nat.factorial j.val : ℂ)) := by
  classical
  unfold finitePoleContour
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pole hpole
  rw [P.meromorphicExponentialKernel_circleIntegral h hM lambda pole
    (by have := Finset.mem_range.mp hpole; omega)]
  congr 1
  have hmu : P.multiplicity pole ≤ M := by
    simpa only [multiplicity, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun a => pole ∈ P.interval a))
  have hr := localCoefficient_reflection P pole h.val
    (fun j => contourExponential lambda P.n (-(pole : ℂ)) * lambda ^ j /
      (Nat.factorial j : ℂ)) hmu
  simpa only [mul_div_assoc, mul_assoc] using hr

end OddPiPowers.ActualIntervals
