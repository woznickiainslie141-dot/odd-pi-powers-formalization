module

public import OddPiPowers.Analysis.ActualHorizontalGeometry

/-! Full denominator lower bounds on both horizontal lines. -/

@[expose] public section

namespace OddPiPowers.ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem normalizedHorizontalProduct_normSq (Y t : ℝ) :
    Complex.normSq (P.normalizedHorizontalProduct Y t) =
      ∏ a : Fin M, ∏ r ∈ P.interval a,
        horizontalFactor Y (P.horizontalOffset r) t := by
  classical
  simp only [normalizedHorizontalProduct, map_prod]
  rfl

theorem interval_horizontal_tail (hn : 0 < P.n) (a : Fin M)
    (Y t : ℝ) (hY : 1 / 2 < Y) :
    (1 + t ^ 2 / horizontalB Y) ^ (P.interval a).card *
      (∏ r ∈ P.interval a, horizontalFactor Y (P.horizontalOffset r) 0) ≤
      ∏ r ∈ P.interval a, horizontalFactor Y (P.horizontalOffset r) t := by
  apply symmetric_horizontal_product _ _ _ _ hY
  · exact fun r hr => P.horizontalOffset_abs_le hn a hr
  · calc
      _ = ∏ r ∈ P.interval a,
          horizontalFactor Y (P.horizontalOffset (P.n - r)) t := by
        apply Finset.prod_congr rfl
        intro r hr
        rw [P.horizontalOffset_reflect hn
          (((P.interval_mem_iff a r).mp hr).2.trans (P.right_le_n a))]
      _ = _ := P.prod_interval_reflect a
        (fun r => horizontalFactor Y (P.horizontalOffset r) t)

theorem normalizedHorizontalProduct_tail (hn : 0 < P.n)
    (Y t : ℝ) (hY : 1 / 2 < Y) :
    (1 + t ^ 2 / horizontalB Y) ^ P.totalMultiplicity *
      Complex.normSq (P.normalizedHorizontalProduct Y 0) ≤
      Complex.normSq (P.normalizedHorizontalProduct Y t) := by
  classical
  have hb : 0 ≤ 1 + t ^ 2 / horizontalB Y := by
    have := horizontalB_pos hY
    positivity
  have h := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun a ha => mul_nonneg (pow_nonneg hb _)
      (Finset.prod_nonneg (fun r hr => (horizontalFactor_pos (by linarith : Y ≠ 0) _ _).le)))
    (fun a ha => P.interval_horizontal_tail hn a Y t hY)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← P.totalMultiplicity_eq_sum_interval_card] at h
  simpa only [P.normalizedHorizontalProduct_normSq] using h

theorem horizontalDenominator_normSq (hn : 0 < P.n) (Y t : ℝ) :
    Complex.normSq (P.horizontalDenominator Y t) =
      (P.n : ℝ) ^ (2 * P.totalMultiplicity) *
        Complex.normSq (P.normalizedHorizontalProduct Y t) := by
  rw [P.horizontalDenominator_eq hn, Complex.normSq_mul, map_pow]
  simp only [Complex.normSq_natCast, ← pow_two, ← pow_mul]

/-- Exact degree exponent, stated with squared norms to avoid fractional
power conventions. Equivalent to the manuscript exponent degree/2. -/
theorem horizontalDenominator_tail_sq (hn : 0 < P.n)
    (Y t : ℝ) (hY : 1 / 2 < Y) :
    (1 + t ^ 2 / horizontalB Y) ^ P.denominator.natDegree *
      ‖P.horizontalDenominator Y 0‖ ^ 2 ≤
      ‖P.horizontalDenominator Y t‖ ^ 2 := by
  rw [P.denominator_natDegree, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, P.horizontalDenominator_normSq hn,
    P.horizontalDenominator_normSq hn]
  have h := mul_le_mul_of_nonneg_left (P.normalizedHorizontalProduct_tail hn Y t hY)
    (show 0 ≤ (P.n : ℝ) ^ (2 * P.totalMultiplicity) by positivity)
  simpa only [mul_left_comm] using h

theorem horizontalDenominator_norm_neg_height (hn : 0 < P.n) (Y t : ℝ) :
    ‖P.horizontalDenominator (-Y) t‖ = ‖P.horizontalDenominator Y t‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    P.horizontalDenominator_normSq hn, P.horizontalDenominator_normSq hn]
  congr 1
  simp only [P.normalizedHorizontalProduct_normSq, horizontalFactor_eq, neg_sq]

/-- Integer half-degree weakening used to dominate every finite row. -/
theorem horizontalDenominator_tail_pow (hn : 0 < P.n)
    (Y t : ℝ) (hY : 1 / 2 < Y) (j : ℕ)
    (hj : 2 * j ≤ P.denominator.natDegree) :
    (1 + t ^ 2 / horizontalB Y) ^ j * ‖P.horizontalDenominator Y 0‖ ≤
      ‖P.horizontalDenominator Y t‖ := by
  have hb : 1 ≤ 1 + t ^ 2 / horizontalB Y := by
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg t) (horizontalB_pos hY).le)
  have hp := pow_le_pow_right₀ hb hj
  have h := (mul_le_mul_of_nonneg_right hp (sq_nonneg ‖P.horizontalDenominator Y 0‖)).trans
    (P.horizontalDenominator_tail_sq hn Y t hY)
  have he : ((1 + t ^ 2 / horizontalB Y) ^ j * ‖P.horizontalDenominator Y 0‖) ^ 2 =
      (1 + t ^ 2 / horizontalB Y) ^ (2 * j) * ‖P.horizontalDenominator Y 0‖ ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm j 2]
  rw [← he] at h
  exact (sq_le_sq₀ (mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _))
    (norm_nonneg _)).mp h

theorem horizontalDenominator_lower_tail_pow (hn : 0 < P.n)
    (Y t : ℝ) (hY : 1 / 2 < Y) (j : ℕ)
    (hj : 2 * j ≤ P.denominator.natDegree) :
    (1 + t ^ 2 / horizontalB Y) ^ j * ‖P.horizontalDenominator (-Y) 0‖ ≤
      ‖P.horizontalDenominator (-Y) t‖ := by
  rw [P.horizontalDenominator_norm_neg_height hn, P.horizontalDenominator_norm_neg_height hn]
  exact P.horizontalDenominator_tail_pow hn Y t hY j hj

end OddPiPowers.ActualIntervals
