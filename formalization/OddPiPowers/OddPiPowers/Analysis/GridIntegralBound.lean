module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A quantitative left-endpoint Riemann estimate on an arithmetic grid. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory
open scoped BigOperators

theorem grid_cell_integral_error {f : ℝ → ℝ} (hf : Continuous f) (K : ℝ)
    (hK : 0 ≤ K) (hLip : ∀ x y, ‖f x - f y‖ ≤ K * |x - y|)
    (s δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    ‖δ * f ((k : ℝ) * δ + s) -
      ∫ x : ℝ in (k : ℝ) * δ + s..((k + 1 : ℕ) : ℝ) * δ + s, f x‖ ≤ K * δ ^ 2 := by
  let a : ℝ := (k : ℝ) * δ + s
  let b : ℝ := ((k + 1 : ℕ) : ℝ) * δ + s
  have hba : b - a = δ := by dsimp [a, b]; push_cast; ring
  have hab : a ≤ b := by linarith
  have he : δ * f a - (∫ x : ℝ in a..b, f x) =
      ∫ x : ℝ in a..b, f a - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, hba, smul_eq_mul]
  have hbnd : ‖∫ x : ℝ in a..b, f a - f x‖ ≤ K * δ ^ 2 := by
    have ht := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := K * δ) (f := fun x => f a - f x) (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        have hx' := (Set.mem_Ioc.mp hx)
        have ha : |a - x| ≤ δ := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        exact (hLip a x).trans (mul_le_mul_of_nonneg_left ha hK))
    simpa only [hba, abs_of_nonneg hδ, pow_two, mul_assoc] using ht
  change ‖δ * f a - (∫ x : ℝ in a..b, f x)‖ ≤ _
  rw [he]
  exact hbnd

theorem grid_integral_error {f : ℝ → ℝ} (hf : Continuous f) (K : ℝ)
    (hK : 0 ≤ K) (hLip : ∀ x y, ‖f x - f y‖ ≤ K * |x - y|)
    (s δ : ℝ) (hδ : 0 ≤ δ) (l u : ℕ) (hlu : l ≤ u) :
    ‖δ * (∑ k ∈ Finset.Ico l u, f ((k : ℝ) * δ + s)) -
      ∫ x : ℝ in (l : ℝ) * δ + s..(u : ℝ) * δ + s, f x‖ ≤
        K * δ ^ 2 * (u - l : ℕ) := by
  have he := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := f) (μ := volume) (a := fun k : ℕ => (k : ℝ) * δ + s) hlu
    (fun k hk => hf.intervalIntegrable _ _)
  rw [← he, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.Ico l u, ‖δ * f ((k : ℝ) * δ + s) -
        ∫ x : ℝ in (k : ℝ) * δ + s..((k + 1 : ℕ) : ℝ) * δ + s, f x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico l u, K * δ ^ 2 := Finset.sum_le_sum
      (fun k hk => grid_cell_integral_error hf K hK hLip s δ hδ k)
    _ = _ := by simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; ring

end OddPiPowers
