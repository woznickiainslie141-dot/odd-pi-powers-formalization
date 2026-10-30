module

public import OddPiPowers.Analysis.HorizontalProduct
public import OddPiPowers.Construction.ActualAuxiliary

/-! Reflection and normalization for the actual denominator polynomial. -/

@[expose] public section

namespace OddPiPowers

noncomputable def horizontalPoint (n : ℕ) (Y t : ℝ) : ℂ :=
  (n : ℂ) * (((t - 1 / 2 : ℝ) : ℂ) + Complex.I * (Y : ℂ))

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

noncomputable def horizontalOffset (r : ℕ) : ℝ := (r : ℝ) / P.n - 1 / 2

noncomputable def horizontalDenominator (Y t : ℝ) : ℂ :=
  P.denominator.eval₂ (Rat.castHom ℂ) (horizontalPoint P.n Y t)

noncomputable def normalizedHorizontalProduct (Y t : ℝ) : ℂ :=
  ∏ a : Fin M, ∏ r ∈ P.interval a,
    (((t + P.horizontalOffset r : ℝ) : ℂ) + Complex.I * (Y : ℂ))

theorem interval_reflect_mem (a : Fin M) {r : ℕ} (hr : r ∈ P.interval a) :
    P.n - r ∈ P.interval a := by
  have h := (P.interval_mem_iff a r).mp hr
  apply (P.interval_mem_iff a _).mpr
  dsimp [right] at *
  omega

theorem prod_interval_reflect {α : Type*} [CommMonoid α]
    (a : Fin M) (f : ℕ → α) :
    (∏ r ∈ P.interval a, f (P.n - r)) = ∏ r ∈ P.interval a, f r := by
  apply Finset.prod_bij (fun r _ => P.n - r)
  · exact fun r hr => P.interval_reflect_mem a hr
  · intro r hr s hs he
    have hrn := ((P.interval_mem_iff a r).mp hr).2.trans (P.right_le_n a)
    have hsn := ((P.interval_mem_iff a s).mp hs).2.trans (P.right_le_n a)
    omega
  · intro r hr
    refine ⟨P.n - r, P.interval_reflect_mem a hr, ?_⟩
    have hrn := ((P.interval_mem_iff a r).mp hr).2.trans (P.right_le_n a)
    omega
  · intros
    rfl

theorem horizontalOffset_reflect (hn : 0 < P.n) {r : ℕ} (hr : r ≤ P.n) :
    P.horizontalOffset (P.n - r) = -P.horizontalOffset r := by
  unfold horizontalOffset
  rw [Nat.cast_sub hr]
  have hn0 : (P.n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem horizontalOffset_abs_le (hn : 0 < P.n) (a : Fin M)
    {r : ℕ} (hr : r ∈ P.interval a) : |P.horizontalOffset r| ≤ 1 / 2 := by
  have hrn : r ≤ P.n := ((P.interval_mem_iff a r).mp hr).2.trans (P.right_le_n a)
  have hn0 : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hdiv : (r : ℝ) / P.n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hrn)
  have hdiv0 : (0 : ℝ) ≤ (r : ℝ) / P.n := by positivity
  rw [horizontalOffset, abs_le]
  constructor <;> linarith

theorem horizontalPoint_add_pole (hn : 0 < P.n) (Y t : ℝ) (r : ℕ) :
    horizontalPoint P.n Y t + (r : ℂ) =
      (P.n : ℂ) * (((t + P.horizontalOffset r : ℝ) : ℂ) +
        Complex.I * (Y : ℂ)) := by
  unfold horizontalPoint horizontalOffset
  push_cast
  have hn0 : (P.n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- Exact connection to the original polynomial, including every endpoint. -/
theorem horizontalDenominator_eq (hn : 0 < P.n) (Y t : ℝ) :
    P.horizontalDenominator Y t =
      (P.n : ℂ) ^ P.totalMultiplicity * P.normalizedHorizontalProduct Y t := by
  classical
  simp only [horizontalDenominator, denominator, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_add, Polynomial.eval₂_X]
  simp only [Polynomial.C_eq_natCast, Polynomial.eval₂_natCast]
  simp_rw [P.horizontalPoint_add_pole hn, Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum,
    ← P.totalMultiplicity_eq_sum_interval_card]
  rfl

theorem normalizedHorizontalProduct_ne_zero (Y t : ℝ) (hY : Y ≠ 0) :
    P.normalizedHorizontalProduct Y t ≠ 0 := by
  classical
  unfold normalizedHorizontalProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr he
  have hi := congrArg Complex.im he
  exact hY (by simpa using hi)

theorem horizontalDenominator_ne_zero (hn : 0 < P.n) (Y t : ℝ) (hY : Y ≠ 0) :
    P.horizontalDenominator Y t ≠ 0 := by
  rw [P.horizontalDenominator_eq hn]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast hn.ne')
  · exact P.normalizedHorizontalProduct_ne_zero Y t hY

theorem denominator_natDegree : P.denominator.natDegree = P.totalMultiplicity := by
  classical
  unfold denominator
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun a ha =>
    Polynomial.monic_prod_of_monic _ _ (fun r hr => Polynomial.monic_X_add_C _))]
  rw [P.totalMultiplicity_eq_sum_interval_card]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Polynomial.natDegree_prod_of_monic (P.interval a)
    (fun r : ℕ => Polynomial.X + Polynomial.C (r : ℚ))
    (fun r hr => Polynomial.monic_X_add_C (r : ℚ))]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

end ActualIntervals
end OddPiPowers
