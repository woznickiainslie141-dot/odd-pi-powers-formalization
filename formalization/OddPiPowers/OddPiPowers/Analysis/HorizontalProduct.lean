module

public import OddPiPowers.Analysis.HorizontalPair
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Whole-line product estimates. Reflection is used on the full product,
so fixed points and repeated factors need no parity convention. -/

@[expose] public section

namespace OddPiPowers

noncomputable def horizontalB (Y : ℝ) : ℝ :=
  (Y ^ 2 + 1 / 4) ^ 2 / (Y ^ 2 - 1 / 4)

theorem horizontalB_pos {Y : ℝ} (hY : 1 / 2 < Y) : 0 < horizontalB Y := by
  unfold horizontalB
  apply div_pos
  · positivity
  · nlinarith

noncomputable def horizontalFactor (Y u t : ℝ) : ℝ :=
  Complex.normSq (((t + u : ℝ) : ℂ) + Complex.I * (Y : ℂ))

theorem horizontalFactor_eq (Y u t : ℝ) :
    horizontalFactor Y u t = (t + u) ^ 2 + Y ^ 2 := by
  exact normSq_horizontal_factor (t + u) Y

theorem horizontalFactor_pos {Y : ℝ} (hY : Y ≠ 0) (u t : ℝ) :
    0 < horizontalFactor Y u t := by
  rw [horizontalFactor_eq]
  nlinarith [sq_pos_of_ne_zero hY, sq_nonneg (t + u)]

theorem horizontal_pair_mul (Y u t : ℝ) (hY : 1 / 2 < Y)
    (hu : |u| ≤ 1 / 2) :
    ((1 + t ^ 2 / horizontalB Y) * horizontalFactor Y u 0) ^ 2 ≤
      horizontalFactor Y u t * horizontalFactor Y (-u) t := by
  have h := horizontal_pair_tail Y u t hY hu
  have hr := paired_normSq_ratio Y u t (by linarith : Y ≠ 0)
  rw [← hr] at h
  have hh := (le_div_iff₀ (show 0 <
      Complex.normSq (((u : ℂ) + Complex.I * (Y : ℂ)) *
      (((-u : ℝ) : ℂ) + Complex.I * (Y : ℂ))) by
        rw [Complex.normSq_mul, normSq_horizontal_factor,
          normSq_horizontal_factor]
        positivity)).mp h
  convert hh using 1 <;>
    simp only [horizontalB, horizontalFactor, Complex.normSq_mul,
      normSq_horizontal_factor, zero_add] <;> ring

/-- Squaring the entire product handles all reflection fixed points, including
an unpaired central factor. `hreflect` is exact finite reindexing. -/
theorem symmetric_horizontal_product {ι : Type*} (s : Finset ι)
    (u : ι → ℝ) (Y t : ℝ) (hY : 1 / 2 < Y)
    (hu : ∀ i ∈ s, |u i| ≤ 1 / 2)
    (hreflect : (∏ i ∈ s, horizontalFactor Y (-u i) t) =
      ∏ i ∈ s, horizontalFactor Y (u i) t) :
    (1 + t ^ 2 / horizontalB Y) ^ s.card *
      (∏ i ∈ s, horizontalFactor Y (u i) 0) ≤
      ∏ i ∈ s, horizontalFactor Y (u i) t := by
  have hbase : 0 ≤ 1 + t ^ 2 / horizontalB Y := by
    have := horizontalB_pos hY
    positivity
  have hprod := Finset.prod_le_prod₀
    (fun i hi => sq_nonneg
      ((1 + t ^ 2 / horizontalB Y) * horizontalFactor Y (u i) 0))
    (fun i hi => horizontal_pair_mul Y (u i) t hY (hu i hi))
  simp only [Finset.prod_pow, Finset.prod_mul_distrib,
    Finset.prod_const, hreflect] at hprod
  rw [← pow_two] at hprod
  apply (sq_le_sq₀ ?_ ?_).mp hprod
  · exact mul_nonneg (pow_nonneg hbase _) (Finset.prod_nonneg
      (fun i hi => (horizontalFactor_pos (by linarith : Y ≠ 0) _ _).le))
  · exact Finset.prod_nonneg
      (fun i hi => (horizontalFactor_pos (by linarith : Y ≠ 0) _ _).le)

end OddPiPowers
