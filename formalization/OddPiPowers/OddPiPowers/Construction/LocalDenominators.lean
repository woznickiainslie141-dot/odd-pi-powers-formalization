module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! A common-denominator calculus for local rational power series.
Regular factors carry an offset of one; pole-unit factors carry zero.
The offset is additive under convolution, independently of pole order. -/

@[expose] public section

namespace OddPiPowers

open scoped PowerSeries BigOperators

/-- The finite lcm used by the local denominator construction. This is
definitionally the same formula as `Nat.lcmUpto` without importing PNT. -/
def intervalLcm (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

theorem intervalLcm_pos (n : ℕ) : 0 < intervalLcm n := by
  have hn : intervalLcm n ≠ 0 := by simp [intervalLcm]
  omega

theorem boundedDistance_dvd_intervalLcm (n : ℕ) (e : ℤ) (he : e ≠ 0)
    (hlen : e.natAbs ≤ n) : e ∣ (intervalLcm n : ℤ) := by
  have hpos : 1 ≤ e.natAbs := Nat.one_le_iff_ne_zero.2 (by simpa using he)
  have hd : e.natAbs ∣ intervalLcm n :=
    Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) (Finset.mem_Icc.2 ⟨hpos, hlen⟩)
  exact Int.natAbs_dvd_natAbs.1 (by simpa using hd)

def integerRationals : Subring ℚ := (Int.castRingHom ℚ).range

theorem intCast_mem_integerRationals (z : ℤ) : (z : ℚ) ∈ integerRationals :=
  ⟨z, rfl⟩

def IntegralCoefficients (f : PowerSeries ℚ) : Prop :=
  ∀ n, PowerSeries.coeff n f ∈ integerRationals

theorem integralCoefficients_one : IntegralCoefficients (1 : PowerSeries ℚ) := by
  intro n
  simp only [PowerSeries.coeff_one]
  split_ifs <;> norm_num [integerRationals, RingHom.mem_range]

theorem integralCoefficients_C (z : ℤ) :
    IntegralCoefficients (PowerSeries.C (z : ℚ)) := by
  intro n
  simp only [PowerSeries.coeff_C]
  split_ifs
  · exact intCast_mem_integerRationals z
  · exact integerRationals.zero_mem

theorem IntegralCoefficients.mul {f g : PowerSeries ℚ}
    (hf : IntegralCoefficients f) (hg : IntegralCoefficients g) :
    IntegralCoefficients (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact integerRationals.sum_mem (fun p _ => integerRationals.mul_mem (hf p.1) (hg p.2))

theorem IntegralCoefficients.add {f g : PowerSeries ℚ}
    (hf : IntegralCoefficients f) (hg : IntegralCoefficients g) :
    IntegralCoefficients (f + g) := by
  intro n
  simpa using integerRationals.add_mem (hf n) (hg n)

theorem integralCoefficients_X : IntegralCoefficients (PowerSeries.X : PowerSeries ℚ) := by
  intro n
  simp only [PowerSeries.coeff_X]
  split_ifs <;> norm_num [integerRationals, RingHom.mem_range]

theorem IntegralCoefficients.pow {f : PowerSeries ℚ}
    (hf : IntegralCoefficients f) (h : ℕ) : IntegralCoefficients (f ^ h) := by
  induction h with
  | zero => simpa using integralCoefficients_one
  | succ h ih => simpa only [pow_succ] using ih.mul hf

noncomputable def scaledLocal (d : ℤ) (b : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.C ((d : ℚ) ^ b) * PowerSeries.rescale (d : ℚ) f

def DenominatorCleared (d : ℤ) (b : ℕ) (f : PowerSeries ℚ) : Prop :=
  IntegralCoefficients (scaledLocal d b f)

theorem denominatorCleared_iff (d : ℤ) (b : ℕ) (f : PowerSeries ℚ) :
    DenominatorCleared d b f ↔
      ∀ n, (d : ℚ) ^ (n + b) * PowerSeries.coeff n f ∈ integerRationals := by
  simp only [DenominatorCleared, IntegralCoefficients, scaledLocal,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, ← mul_assoc, ← pow_add]
  simp only [Nat.add_comm b]

theorem scaledLocal_mul (d : ℤ) (b c : ℕ) (f g : PowerSeries ℚ) :
    scaledLocal d (b + c) (f * g) = scaledLocal d b f * scaledLocal d c g := by
  simp only [scaledLocal, pow_add, map_mul]
  ring

theorem DenominatorCleared.mul {d : ℤ} {b c : ℕ} {f g : PowerSeries ℚ}
    (hf : DenominatorCleared d b f) (hg : DenominatorCleared d c g) :
    DenominatorCleared d (b + c) (f * g) := by
  change IntegralCoefficients (scaledLocal d (b + c) (f * g))
  rw [scaledLocal_mul]
  exact IntegralCoefficients.mul hf hg

theorem DenominatorCleared.add {d : ℤ} {b : ℕ} {f g : PowerSeries ℚ}
    (hf : DenominatorCleared d b f) (hg : DenominatorCleared d b g) :
    DenominatorCleared d b (f + g) := by
  change IntegralCoefficients (scaledLocal d b (f + g))
  simpa only [scaledLocal, map_add, mul_add] using IntegralCoefficients.add hf hg

theorem denominatorCleared_one (d : ℤ) :
    DenominatorCleared d 0 (1 : PowerSeries ℚ) := by
  simpa [DenominatorCleared, scaledLocal] using integralCoefficients_one

theorem denominatorCleared_of_integralCoefficients (d : ℤ) (f : PowerSeries ℚ)
    (hf : IntegralCoefficients f) : DenominatorCleared d 0 f := by
  rw [denominatorCleared_iff]
  intro n
  simpa using integerRationals.mul_mem (intCast_mem_integerRationals (d ^ n)) (hf n)

/-- The polynomial numerator `(-ell+w)^h` has no extra denominator offset. -/
theorem polynomialNumerator_cleared (d ell : ℤ) (h : ℕ) :
    DenominatorCleared d 0 ((PowerSeries.C (-ell : ℚ) + PowerSeries.X) ^ h) := by
  apply denominatorCleared_of_integralCoefficients
  exact (IntegralCoefficients.add (by simpa using integralCoefficients_C (-ell))
    integralCoefficients_X).pow h

theorem denominatorCleared_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (d : ℤ) (b : ι → ℕ) (f : ι → PowerSeries ℚ)
    (hf : ∀ i ∈ s, DenominatorCleared d (b i) (f i)) :
    DenominatorCleared d (∑ i ∈ s, b i) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using denominatorCleared_one d
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hf i (by simp)).mul (ih (fun j hj => hf j (by simp [hj])))

/-- The normalized reciprocal has coefficients `(-1/e)^n`. -/
noncomputable def normalizedReciprocal (e : ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (-1 / (e : ℚ)) ^ n)

noncomputable def regularReciprocal (e : ℤ) : PowerSeries ℚ :=
  PowerSeries.C (1 / (e : ℚ)) * normalizedReciprocal e

theorem normalizedReciprocal_identity (e : ℤ) :
    (1 + PowerSeries.C (1 / (e : ℚ)) * PowerSeries.X) * normalizedReciprocal e = 1 := by
  rw [add_mul, one_mul, mul_assoc]
  ext n
  cases n with
  | zero => simp [normalizedReciprocal]
  | succ n =>
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      normalizedReciprocal, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      Nat.succ_ne_zero, ite_false, pow_succ]
    ring

theorem regularReciprocal_identity (e : ℤ) (he : e ≠ 0) :
    (PowerSeries.C (e : ℚ) + PowerSeries.X) * regularReciprocal e = 1 := by
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have hc : PowerSeries.C (e : ℚ) * PowerSeries.C (1 / (e : ℚ)) =
      (1 : PowerSeries ℚ) := by
    rw [← map_mul]
    simp [he']
  calc
    _ = (PowerSeries.C (e : ℚ) * PowerSeries.C (1 / (e : ℚ))) * normalizedReciprocal e +
        (PowerSeries.C (1 / (e : ℚ)) * PowerSeries.X) * normalizedReciprocal e := by
      dsimp [regularReciprocal]
      ring
    _ = (1 + PowerSeries.C (1 / (e : ℚ)) * PowerSeries.X) * normalizedReciprocal e := by
      rw [hc]
      ring
    _ = 1 := normalizedReciprocal_identity e

theorem normalizedReciprocal_cleared (d e : ℤ) (he : e ≠ 0) (hed : e ∣ d) :
    DenominatorCleared d 0 (normalizedReciprocal e) := by
  rw [denominatorCleared_iff]
  obtain ⟨z, hz⟩ := hed
  have heq : (d : ℚ) * (-1 / (e : ℚ)) = ((-z : ℤ) : ℚ) := by
    have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he
    rw [hz, Int.cast_mul]
    push_cast
    field_simp [he']
  intro n
  have hpow : (d : ℚ) ^ n * (-1 / (e : ℚ)) ^ n = (((-z) ^ n : ℤ) : ℚ) := by
    rw [← mul_pow, heq, Int.cast_pow]
  simpa only [normalizedReciprocal, PowerSeries.coeff_mk, Nat.add_zero, hpow]
    using intCast_mem_integerRationals ((-z) ^ n)

theorem denominatorCleared_C (d : ℤ) (b : ℕ) (a : ℚ)
    (ha : (d : ℚ) ^ b * a ∈ integerRationals) :
    DenominatorCleared d b (PowerSeries.C a) := by
  rw [denominatorCleared_iff]
  intro n
  by_cases hn : n = 0
  · simpa [hn] using ha
  · simp [PowerSeries.coeff_C, hn]

theorem regularReciprocal_cleared (d e : ℤ) (he : e ≠ 0) (hed : e ∣ d) :
    DenominatorCleared d 1 (regularReciprocal e) := by
  have hc : DenominatorCleared d 1 (PowerSeries.C (1 / (e : ℚ))) := by
    apply denominatorCleared_C
    obtain ⟨z, hz⟩ := hed
    have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he
    have hh : (d : ℚ) ^ 1 * (1 / (e : ℚ)) = (z : ℚ) := by
      rw [hz, Int.cast_mul]
      field_simp [he']
    rw [hh]
    exact intCast_mem_integerRationals z
  simpa only [Nat.add_zero, regularReciprocal] using
    hc.mul (normalizedReciprocal_cleared d e he hed)

theorem normalizedReciprocal_intervalLcm (n : ℕ) (e : ℤ) (he : e ≠ 0)
    (hlen : e.natAbs ≤ n) :
    DenominatorCleared (intervalLcm n) 0 (normalizedReciprocal e) :=
  normalizedReciprocal_cleared _ e he (boundedDistance_dvd_intervalLcm n e he hlen)

theorem regularReciprocal_intervalLcm (n : ℕ) (e : ℤ) (he : e ≠ 0)
    (hlen : e.natAbs ≤ n) :
    DenominatorCleared (intervalLcm n) 1 (regularReciprocal e) :=
  regularReciprocal_cleared _ e he (boundedDistance_dvd_intervalLcm n e he hlen)

theorem denominatorCleared_sum {ι : Type*} (s : Finset ι) (d : ℤ) (b : ℕ)
    (f : ι → PowerSeries ℚ) (hf : ∀ i ∈ s, DenominatorCleared d b (f i)) :
    DenominatorCleared d b (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [denominatorCleared_iff]
    simp only [Finset.sum_empty, map_zero, mul_zero]
    exact fun _ => integerRationals.zero_mem
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

/-- An integer weighted partial-fraction sum has offset one, regardless of
the number of summands. This is the regular-factor compression. -/
theorem regularLocalSum_cleared {ι : Type*} (s : Finset ι) (d : ℤ)
    (w e : ι → ℤ) (he : ∀ i ∈ s, e i ≠ 0) (hed : ∀ i ∈ s, e i ∣ d) :
    DenominatorCleared d 1
      (∑ i ∈ s, PowerSeries.C (w i : ℚ) * regularReciprocal (e i)) := by
  apply denominatorCleared_sum
  intro i hi
  have hw : DenominatorCleared d 0 (PowerSeries.C (w i : ℚ)) := by
    apply denominatorCleared_C
    simp
  simpa using hw.mul (regularReciprocal_cleared d (e i) (he i hi) (hed i hi))

/-- A pole-unit product has offset zero, regardless of how many reciprocal
linear factors it contains. -/
theorem poleLocalProduct_cleared {ι : Type*} [DecidableEq ι] (s : Finset ι) (d z : ℤ)
    (e : ι → ℤ) (he : ∀ i ∈ s, e i ≠ 0) (hed : ∀ i ∈ s, e i ∣ d) :
    DenominatorCleared d 0
      (PowerSeries.C (z : ℚ) * ∏ i ∈ s, normalizedReciprocal (e i)) := by
  have hz : DenominatorCleared d 0 (PowerSeries.C (z : ℚ)) := by
    apply denominatorCleared_C
    simp
  have hp := denominatorCleared_prod s d (fun _ => 0)
    (fun i => normalizedReciprocal (e i))
    (fun i hi => normalizedReciprocal_cleared d (e i) (he i hi) (hed i hi))
  simpa using hz.mul hp

/-- A larger total exponent clears any coefficient within the budget. -/
theorem DenominatorCleared.coeff_with_budget {d : ℤ} {b : ℕ} {f : PowerSeries ℚ}
    (hf : DenominatorCleared d b f) (u B : ℕ) (hu : u + b ≤ B) :
    (d : ℚ) ^ B * PowerSeries.coeff u f ∈ integerRationals := by
  have hc := (denominatorCleared_iff d b f).1 hf u
  have hi := integerRationals.mul_mem
    (intCast_mem_integerRationals (d ^ (B - (u + b)))) hc
  have hB : B - (u + b) + (u + b) = B := Nat.sub_add_cancel hu
  simpa only [Int.cast_pow, ← mul_assoc, ← pow_add, hB] using hi

theorem pole_regular_order_budget (M μ j u : ℕ) (hμ : μ ≤ M)
    (hj : j + 1 ≤ μ) (hu : u ≤ μ - 1 - j) :
    u + (M - μ) ≤ (M - 1) - j := by
  omega

/-- The combined coefficient budget for the actual split into pole factors
and regular factors. Each pole contributes offset zero and each regular
factor offset one; the extraction order cancels the variable multiplicity. -/
theorem mixedLocalProduct_coefficient {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (poles : Finset ι) (regular : Finset κ) (d : ℤ)
    (fp : ι → PowerSeries ℚ) (fr : κ → PowerSeries ℚ)
    (hp : ∀ i ∈ poles, DenominatorCleared d 0 (fp i))
    (hr : ∀ i ∈ regular, DenominatorCleared d 1 (fr i))
    (j u : ℕ) (hj : j + 1 ≤ poles.card) (hu : u ≤ poles.card - 1 - j) :
    (d : ℚ) ^ ((poles.card + regular.card - 1) - j) *
      PowerSeries.coeff u ((∏ i ∈ poles, fp i) * (∏ i ∈ regular, fr i))
        ∈ integerRationals := by
  have hp' := denominatorCleared_prod poles d (fun _ => 0) fp hp
  have hr' := denominatorCleared_prod regular d (fun _ => 1) fr hr
  have hc : DenominatorCleared d regular.card
      ((∏ i ∈ poles, fp i) * (∏ i ∈ regular, fr i)) := by
    simpa using hp'.mul hr'
  apply hc.coeff_with_budget
  omega

end OddPiPowers
