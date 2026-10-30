module

public import OddPiPowers.Arithmetic.FinitePeriodKernel
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! A finite rational tail from an algebraic telescoper.
The one-step defect has a positive polynomial numerator. No integration,
infinite sum, or exchange of limits is needed. -/

@[expose] public section
open scoped BigOperators
namespace OddPiPowers.PrimeRates

noncomputable def periodTailPrimitive (r : ℕ) (a b : ℝ) : ℝ :=
  (b - a) / ((r : ℝ) + a) - ((b - a) / ((r : ℝ) + a)) ^ 2 / 2 +
    periodGap r a b / 2

theorem rational_tail_step_identity (t d : ℝ) (ht : 0 < t) (hd : 0 < d) :
    d / (t * (t + d)) -
      ((d / t - (d / t) ^ 2 / 2 + d / (t * (t + d)) / 2) -
        (d / (t + 1) - (d / (t + 1)) ^ 2 / 2 +
          d / ((t + 1) * (t + 1 + d)) / 2)) =
      d * (t * (t + 1) + (2 * t ^ 2 + 2 * t + 1) * d ^ 2 +
        (2 * t + 1) * d ^ 3) /
      (2 * t ^ 2 * (t + 1) ^ 2 * (t + d) * (t + d + 1)) := by
  have ht1 : t + 1 ≠ 0 := by positivity
  have htd : t + d ≠ 0 := by positivity
  have ht1d : t + 1 + d ≠ 0 := by positivity
  have htd1 : t + d + 1 ≠ 0 := by positivity
  field_simp [ht.ne', ht1, htd, ht1d, htd1] <;> ring

theorem periodTailPrimitive_step (r : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    periodTailPrimitive r a b - periodTailPrimitive (r + 1) a b ≤ periodGap r a b := by
  have ht : (0 : ℝ) < (r : ℝ) + a := by positivity
  have hd : 0 < b - a := sub_pos.mpr hab
  have he := rational_tail_step_identity ((r : ℝ) + a) (b - a) ht hd
  have hp : 0 ≤ (b-a) * (((r : ℝ)+a) * (((r : ℝ)+a)+1) +
      (2 * ((r : ℝ)+a)^2 + 2 * ((r : ℝ)+a) + 1) * (b-a)^2 +
        (2 * ((r : ℝ)+a)+1) * (b-a)^3) /
      (2 * ((r : ℝ)+a)^2 * (((r : ℝ)+a)+1)^2 *
        (((r : ℝ)+a)+(b-a)) * (((r : ℝ)+a)+(b-a)+1)) := by positivity
  have hn := he.symm ▸ hp
  unfold periodTailPrimitive
  rw [periodGap_eq_fraction r ha hab.le, periodGap_eq_fraction (r + 1) ha hab.le]
  push_cast
  have h1 : (r : ℝ) + a + (b - a) = (r : ℝ) + b := by ring
  have h2 : (r : ℝ) + a + 1 = (r : ℝ) + 1 + a := by ring
  have h3 : (r : ℝ) + a + 1 + (b - a) = (r : ℝ) + 1 + b := by ring
  rw [h1, h3, h2] at hn
  linarith

theorem periodTailPrimitive_sum (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (T K : ℕ) (hTK : T ≤ K) :
    periodTailPrimitive T a b - periodTailPrimitive K a b ≤
      ∑ r ∈ Finset.Ico T K, periodGap r a b := by
  induction K, hTK using Nat.le_induction with
  | base => simp
  | succ K hTK ih =>
    have hs := periodTailPrimitive_step K a b ha hab
    rw [Finset.sum_Ico_succ_top (by omega : T ≤ K)]
    linarith

theorem periodGap_finite_rational_lower (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (T K : ℕ) (_hT : 1 ≤ T) (hTK : T ≤ K) :
    ((b-a) / ((T : ℝ) + a)) - ((b-a) / ((T : ℝ) + a)) ^ 2 / 2 -
      ((b-a) / ((K : ℝ) + a)) + (periodGap T a b - periodGap K a b) / 2 ≤
        ∑ r ∈ Finset.Ico T K, periodGap r a b := by
  have ht := periodTailPrimitive_sum a b ha hab T K hTK
  unfold periodTailPrimitive at ht
  nlinarith [sq_nonneg ((b - a) / ((K : ℝ) + a))]

end OddPiPowers.PrimeRates
