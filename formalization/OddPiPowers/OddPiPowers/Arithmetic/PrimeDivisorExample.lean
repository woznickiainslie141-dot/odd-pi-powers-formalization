module

public import OddPiPowers.Arithmetic.ReducedAuxiliary

@[expose] public section

namespace OddPiPowers

namespace ActualIntervals

def exampleIntervals42 : ActualIntervals 2 where
  n := 42
  left := fun a => a.val * 3
  left_mono := by
    intro a b hab
    exact Nat.mul_le_mul_right 3 (Fin.le_iff_val_le_val.mp hab)
  left_bound := by
    intro a
    have ha := a.isLt
    simp
    omega

theorem prime41 : Nat.Prime 41 := by decide

theorem example42_prime_conditions : 41 ≤ exampleIntervals42.n ∧
    exampleIntervals42.n < 41 * 41 := by
  norm_num [exampleIntervals42]

/-- Kernel evaluation of all 43 signed-floor carry totals for the chosen
nontrivial two-interval example. -/
theorem example42_carryWeight_ge_one (ell : Fin 43) :
    exampleIntervals42.carryWeight 41 ell.val ≥ 1 := by
  fin_cases ell <;> decide

theorem example42_coeff_divisible_41 (h j : Fin 2) (k : ℕ) :
    (41 : ℤ) ∣ (actualAuxiliaryInt exampleIntervals42 h j).coeff k := by
  by_cases hk : k ≤ 42
  · letI : Fact (Nat.Prime 41) := ⟨prime41⟩
    let hellFin : Fin 43 := ⟨42 - k, by omega⟩
    have hW : 1 ≤ exampleIntervals42.carryWeight 41 (42 - k) := by
      have h := example42_carryWeight_ge_one hellFin
      have hv : hellFin.val = 42 - k := by simp [hellFin]
      rw [hv] at h
      exact h
    have hdiv := actualAuxiliaryInt_coeff_primePower_dvd_all
      (P := exampleIntervals42) (p := 41) (k := k) h j
      (by norm_num [exampleIntervals42]) (by norm_num [exampleIntervals42])
    have hpow : (41 : ℤ) ^ 1 ∣
        (41 : ℤ) ^ (exampleIntervals42.carryWeight 41 (42 - k) + j.val) := by
      exact pow_dvd_pow _ (Nat.le_add_right_of_le hW)
    have hdiv' : (41 : ℤ) ^ 1 ∣
        (actualAuxiliaryInt exampleIntervals42 h j).coeff k := by
      simpa [exampleIntervals42] using dvd_trans hpow hdiv
    simpa using hdiv'
  · have hdeg : (actualAuxiliary exampleIntervals42 h j).natDegree < k := by
      have hbound : (actualAuxiliary exampleIntervals42 h j).natDegree ≤ 42 := by
        calc
          _ ≤ exampleIntervals42.n - exampleIntervals42.left j :=
            actualAuxiliary_natDegree_le exampleIntervals42 h j
          _ ≤ exampleIntervals42.n := Nat.sub_le _ _
          _ = 42 := rfl
      omega
    have hzeroQ : (actualAuxiliary exampleIntervals42 h j).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
    have hcast := actualAuxiliaryInt_coeff_cast exampleIntervals42 h j k
    have hzero : (actualAuxiliaryInt exampleIntervals42 h j).coeff k = 0 := by
      exact_mod_cast (hcast.trans hzeroQ)
    simp [hzero]

end ActualIntervals

end OddPiPowers

end
