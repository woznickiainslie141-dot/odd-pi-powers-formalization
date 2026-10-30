module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators

namespace OddPiPowers.PrimeRates

/-- The logarithmic gap contributed by the interval `(a, b)` at period `r`. -/
noncomputable def periodGap (r : ℕ) (a b : ℝ) : ℝ :=
  1 / ((r : ℝ) + a) - 1 / ((r : ℝ) + b)

theorem periodGap_eq_fraction (r : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    periodGap r a b =
      (b - a) / (((r : ℝ) + a) * ((r : ℝ) + b)) := by
  have hra : 0 < (r : ℝ) + a :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) ha
  have hrb : 0 < (r : ℝ) + b :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) (ha.trans_le hab)
  unfold periodGap
  field_simp [ne_of_gt hra, ne_of_gt hrb] <;> ring

theorem periodGap_pos (r : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < periodGap r a b := by
  rw [periodGap_eq_fraction r ha hab.le]
  exact div_pos (sub_pos.mpr hab)
    (mul_pos
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) ha)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) (ha.trans hab)))

theorem periodGap_nonneg (r : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ periodGap r a b := by
  rw [periodGap_eq_fraction r ha hab]
  exact div_nonneg (sub_nonneg.mpr hab)
    (le_of_lt (mul_pos
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) ha)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) (ha.trans_le hab))))

/-- Moving both endpoints inward can only reduce their contribution. -/
theorem periodGap_antitone_endpoints (r : ℕ) {a a' b' b : ℝ}
    (ha : 0 < a) (haa : a ≤ a') (hab : a' < b') (hbb : b' ≤ b) :
    periodGap r a' b' ≤ periodGap r a b := by
  have ha' : 0 < a' := ha.trans_le haa
  have hb' : 0 < b' := ha'.trans hab
  have hra : 0 < (r : ℝ) + a :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) ha
  have hrb' : 0 < (r : ℝ) + b' :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) hb'
  have haaR : (r : ℝ) + a ≤ (r : ℝ) + a' := by
    simpa only [add_comm] using add_le_add_left haa (r : ℝ)
  have hbbR : (r : ℝ) + b' ≤ (r : ℝ) + b := by
    simpa only [add_comm] using add_le_add_left hbb (r : ℝ)
  have hleft : 1 / ((r : ℝ) + a') ≤ 1 / ((r : ℝ) + a) :=
    one_div_le_one_div_of_le hra haaR
  have hright : 1 / ((r : ℝ) + b) ≤ 1 / ((r : ℝ) + b') :=
    one_div_le_one_div_of_le hrb' hbbR
  unfold periodGap
  exact sub_le_sub hleft hright

/-- Increasing the period reduces the gap, for a positive interval. -/
theorem periodGap_antitone_period (r s : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hrs : r ≤ s) :
    periodGap s a b ≤ periodGap r a b := by
  rw [periodGap_eq_fraction s ha hab.le, periodGap_eq_fraction r ha hab.le]
  have hrs' : (r : ℝ) ≤ (s : ℝ) := Nat.cast_le.mpr hrs
  have hra : 0 < (r : ℝ) + a :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) ha
  have hrb : 0 < (r : ℝ) + b :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) (ha.trans hab)
  have hsa : 0 < (s : ℝ) + a :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg s) ha
  have hdenA : (r : ℝ) + a ≤ (s : ℝ) + a := by
    simpa only [add_comm] using add_le_add_right hrs' a
  have hdenB : (r : ℝ) + b ≤ (s : ℝ) + b := by
    simpa only [add_comm] using add_le_add_right hrs' b
  have hden : ((r : ℝ) + a) * ((r : ℝ) + b) ≤
      ((s : ℝ) + a) * ((s : ℝ) + b) := by
    apply mul_le_mul
      hdenA
      hdenB
      (le_of_lt hrb)
      (le_of_lt hsa)
  exact div_le_div_of_nonneg_left (le_of_lt (sub_pos.mpr hab))
    (mul_pos
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) ha)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) (ha.trans hab)))
    hden

/-- A finite nonnegative weighted sum of positive-period gaps is nonnegative. -/
theorem periodGap_weighted_sum_nonneg {ι : Type*} (s : Finset ι)
    (r : ℕ) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, 0 < a i)
    (hab : ∀ i ∈ s, a i < b i) :
    0 ≤ ∑ i ∈ s, w i * periodGap r (a i) (b i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i hi)
    (le_of_lt (periodGap_pos r (ha i hi) (hab i hi)))

/-- Finite weighted sums distribute over the two reciprocal endpoint sums. -/
theorem periodGap_weighted_sum_eq {ι : Type*} (s : Finset ι)
    (r : ℕ) (w a b : ι → ℝ) :
    (∑ i ∈ s, w i * periodGap r (a i) (b i)) =
      (∑ i ∈ s, w i / ((r : ℝ) + a i)) -
        (∑ i ∈ s, w i / ((r : ℝ) + b i)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [periodGap]
  ring

theorem periodGap_rational_calibration :
    (1 : ℝ) / 69 < 3 / 206 ∧
    (3 : ℝ) / 206 < 3 / 205 ∧
    (3 : ℝ) / 205 < 1 / 68 ∧
    (6 : ℝ) / 69 * periodGap 0 (3 / 206) (3 / 205) = 2 / 69 := by
  norm_num [periodGap]

end OddPiPowers.PrimeRates

end
