module

public import OddPiPowers.Analysis.RectangleCircleComparison
public import OddPiPowers.Analysis.ActualPoleContour

/-! Finite rectangular boundaries equal the actual sum of pole circles. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

open Complex MeasureTheory

variable {M : ℕ} (P : ActualIntervals M)

theorem actual_pole_inside_rectangle (a b : ℝ) (ha : a < -(P.n : ℝ)) (hb : 0 < b)
    (r : ℕ) (hr : r ≤ P.n) : a < -(r : ℝ) ∧ -(r : ℝ) < b := by
  have hrn : (r : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast hr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r]

theorem principalExponentialTerm_rectangleIntegrable (h : ℕ) (lambda : ℂ)
    (a b c d : ℝ) (ha : a < -(P.n : ℝ)) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (r q : ℕ) (hr : r ≤ P.n) :
    RectangleIntegrable (P.principalExponentialTerm h lambda r q) a b c d := by
  have hp := P.actual_pole_inside_rectangle a b ha hb r hr
  have hi := rectangleIntegrable_pole (contourExponential lambda P.n)
    (contourExponential_continuous lambda P.n) (-(r : ℝ)) a b c d
    hp.1.ne hp.2.ne' hc.ne hd.ne' (P.multiplicity r - q)
  unfold principalExponentialTerm
  simpa only [Complex.ofReal_neg, Complex.ofReal_natCast, sub_neg_eq_add] using
    hi.const_mul (((PowerSeries.coeff q (P.localExpansion r h) : ℚ) : ℂ))

theorem principalExponentialTerm_rectangle_eq_circle (h : ℕ) (lambda : ℂ)
    (a b c d : ℝ) (ha : a < -(P.n : ℝ)) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (r q : ℕ) (hr : r ≤ P.n) (hq : q < P.multiplicity r) :
    rectangleIntegral (P.principalExponentialTerm h lambda r q) a b c d =
      ∮ z in C(-(r : ℂ), 1 / 4), P.principalExponentialTerm h lambda r q z := by
  have hp := P.actual_pole_inside_rectangle a b ha hb r hr
  have he : P.multiplicity r - q = (P.multiplicity r - 1 - q) + 1 := by omega
  unfold principalExponentialTerm
  rw [rectangleIntegral_const_mul, circleIntegral.integral_const_mul]
  congr 1
  have ht := rectangleIntegral_real_pole_eq_circle (-(r : ℝ)) a b c d
    hp.1 hp.2 hc hd (P.multiplicity r - 1 - q) (contourExponential lambda P.n)
      (contourExponential_differentiable lambda P.n)
  simpa only [he, Complex.ofReal_neg, Complex.ofReal_natCast, sub_neg_eq_add] using ht

theorem meromorphicExponentialKernel_rectangle_eq_finitePoleContour
    (h : Fin M) (hM : 0 < M) (lambda : ℂ) (a b c d : ℝ)
    (ha : a < -(P.n : ℝ)) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectangleIntegral (P.meromorphicExponentialKernel h.val lambda) a b c d =
      P.finitePoleContour h.val lambda := by
  classical
  let S : ℂ → ℂ := fun z => ∑ r ∈ Finset.range (P.n + 1),
    ∑ q ∈ Finset.range (P.multiplicity r), P.principalExponentialTerm h.val lambda r q z
  have hsum (z : ℂ) (hz : ∀ r : ℕ, r ≤ P.n → z + (r : ℂ) ≠ 0) :
      P.meromorphicExponentialKernel h.val lambda z = S z :=
    P.meromorphicExponentialKernel_principalSum h hM lambda z hz
  have hbot : (fun x : ℝ => P.meromorphicExponentialKernel h.val lambda
      ((x : ℂ) + (c : ℂ) * Complex.I)) =
      (fun x : ℝ => S ((x : ℂ) + (c : ℂ) * Complex.I)) := by
    funext x
    apply hsum
    intro r hr
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast, sub_neg_eq_add] using
      rectangle_horizontal_ne_pole (-(r : ℝ)) c x hc.ne
  have htop : (fun x : ℝ => P.meromorphicExponentialKernel h.val lambda
      ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (fun x : ℝ => S ((x : ℂ) + (d : ℂ) * Complex.I)) := by
    funext x
    apply hsum
    intro r hr
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast, sub_neg_eq_add] using
      rectangle_horizontal_ne_pole (-(r : ℝ)) d x hd.ne'
  have hright : (fun y : ℝ => P.meromorphicExponentialKernel h.val lambda
      ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => S ((b : ℂ) + (y : ℂ) * Complex.I)) := by
    funext y
    apply hsum
    intro r hr
    have hp := P.actual_pole_inside_rectangle a b ha hb r hr
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast, sub_neg_eq_add] using
      rectangle_vertical_ne_pole (-(r : ℝ)) b y hp.2.ne'
  have hleft : (fun y : ℝ => P.meromorphicExponentialKernel h.val lambda
      ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => S ((a : ℂ) + (y : ℂ) * Complex.I)) := by
    funext y
    apply hsum
    intro r hr
    have hp := P.actual_pole_inside_rectangle a b ha hb r hr
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast, sub_neg_eq_add] using
      rectangle_vertical_ne_pole (-(r : ℝ)) a y hp.1.ne
  have hcongr : rectangleIntegral (P.meromorphicExponentialKernel h.val lambda) a b c d =
      rectangleIntegral S a b c d := by
    unfold rectangleIntegral
    rw [hbot, htop, hright, hleft]
  have hint (r : ℕ) (hr : r ∈ Finset.range (P.n + 1)) :
      RectangleIntegrable (fun z => ∑ q ∈ Finset.range (P.multiplicity r),
        P.principalExponentialTerm h.val lambda r q z) a b c d :=
    RectangleIntegrable.fun_sum _ _ a b c d (fun q hq =>
      P.principalExponentialTerm_rectangleIntegrable h.val lambda a b c d ha hb hc hd r q
        (by have := Finset.mem_range.mp hr; omega))
  rw [hcongr]
  dsimp only [S]
  rw [rectangleIntegral_fun_sum _ _ a b c d hint, finitePoleContour]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r ≤ P.n := by have := Finset.mem_range.mp hr; omega
  rw [rectangleIntegral_fun_sum _ _ a b c d (fun q hq =>
    P.principalExponentialTerm_rectangleIntegrable h.val lambda a b c d ha hb hc hd r q hrn),
    P.meromorphicExponentialKernel_circleIntegral h hM lambda r hrn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [P.principalExponentialTerm_rectangle_eq_circle h.val lambda a b c d ha hb hc hd r q hrn
    (Finset.mem_range.mp hq),
    P.principalExponentialTerm_circleIntegral h.val lambda r r q (Finset.mem_range.mp hq),
    ite_eq_left rfl]

end OddPiPowers.ActualIntervals
