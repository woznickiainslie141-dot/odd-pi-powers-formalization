module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Fixed-order coefficient bounds with polynomial, rather than exponential,
dependence on the number of reciprocal factors. Repeated factors remain in a list. -/

@[expose] public section

namespace OddPiPowers

open scoped PowerSeries BigOperators

theorem coeff_mul_abs_le_sum (f g : PowerSeries ℚ) (q : ℕ) :
    |PowerSeries.coeff q (f * g)| ≤
      ∑ i ∈ Finset.range (q + 1), |PowerSeries.coeff i f| * |PowerSeries.coeff (q - i) g| := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun i => PowerSeries.coeff i f * PowerSeries.coeff (q - i) g) (Finset.range (q + 1))

theorem sum_choose_coefficient_majorant (T q : ℕ) :
    (∑ i ∈ Finset.range (q + 1), ((T + i).choose i : ℚ)) =
      ((T + 1 + q).choose q : ℚ) := by
  calc
    _ = ∑ i ∈ Finset.range (q + 1), ((i + T).choose T : ℚ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.add_comm T i, Nat.choose_symm_add]
    _ = ((q + T + 1).choose (T + 1) : ℚ) := by
      exact_mod_cast Nat.sum_range_add_choose q T
    _ = _ := by
      rw [show q + T + 1 = T + 1 + q by omega, Nat.choose_symm_add]

theorem coeff_list_prod_abs_le (l : List (PowerSeries ℚ × ℚ))
    (hB : ∀ p ∈ l, 0 ≤ p.2) (hf : ∀ p ∈ l, ∀ q, |PowerSeries.coeff q p.1| ≤ p.2)
    (q : ℕ) :
    |PowerSeries.coeff q ((l.map Prod.fst).prod)| ≤
      (l.map Prod.snd).prod * ((l.length + q).choose q : ℚ) := by
  induction l generalizing q with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil, zero_add, Nat.choose_self,
      Nat.cast_one, one_mul, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | cons p l ih =>
    have hlB : ∀ x ∈ l, 0 ≤ x.2 := fun x hx => hB x (by simp [hx])
    have hlf : ∀ x ∈ l, ∀ k, |PowerSeries.coeff k x.1| ≤ x.2 :=
      fun x hx => hf x (by simp [hx])
    have hpB : 0 ≤ p.2 := hB p (by simp)
    have hp (k : ℕ) := hf p (by simp) k
    have hprod : 0 ≤ (l.map Prod.snd).prod := List.prod_nonneg (by
      intro b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
      exact hlB x hx)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [mul_comm p.1]
    calc
      _ ≤ ∑ i ∈ Finset.range (q + 1), |PowerSeries.coeff i ((l.map Prod.fst).prod)| *
          |PowerSeries.coeff (q - i) p.1| := coeff_mul_abs_le_sum _ _ q
      _ ≤ ∑ i ∈ Finset.range (q + 1),
          ((l.map Prod.snd).prod * ((l.length + i).choose i : ℚ)) * p.2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul (ih hlB hlf i) (hp (q - i)) (abs_nonneg _) (by positivity)
      _ = (p.2 * (l.map Prod.snd).prod) *
          ∑ i ∈ Finset.range (q + 1), ((l.length + i).choose i : ℚ) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [sum_choose_coefficient_majorant]

theorem choose_coefficient_majorant_le_pow (T q m : ℕ) (hq : q ≤ m) :
    ((T + q).choose q : ℚ) ≤ ((T + m + 1 : ℕ) : ℚ) ^ m := by
  have h1 : (T + q).choose q ≤ (T + q) ^ q := Nat.choose_le_pow _ _
  have h2 : (T + q) ^ q ≤ (T + m + 1) ^ q := Nat.pow_le_pow_left (by omega) q
  have h3 : (T + m + 1) ^ q ≤ (T + m + 1) ^ m :=
    Nat.pow_le_pow_right (by omega) hq
  exact_mod_cast h1.trans (h2.trans h3)

end OddPiPowers
