module

public import OddPiPowers.Arithmetic.SignedCarry
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

@[expose] public section

namespace OddPiPowers

open scoped BigOperators PowerSeries

/-- A zero-safe lower bound for the p-adic valuation. This explicitly handles
zero because `padicValRat p 0` is defined to be zero. -/
def PrimeValuationLowerBound (p : ℕ) (b : ℤ) (q : ℚ) : Prop :=
  q = 0 ∨ b ≤ padicValRat p q

theorem primeValuationLowerBound_zero (p : ℕ) (b : ℤ) :
    PrimeValuationLowerBound p b 0 := Or.inl rfl

theorem primeValuationLowerBound_mono {p : ℕ} {b c : ℤ} {q : ℚ}
    (h : PrimeValuationLowerBound p b q) (hcb : c ≤ b) :
    PrimeValuationLowerBound p c q := by
  rcases h with hq | hq
  · exact Or.inl hq
  · exact Or.inr (le_trans hcb hq)

theorem primeValuationLowerBound_add {p : ℕ} [Fact p.Prime] {b : ℤ} {q r : ℚ}
    (hq : PrimeValuationLowerBound p b q)
    (hr : PrimeValuationLowerBound p b r) :
    PrimeValuationLowerBound p b (q + r) := by
  rcases hq with hq | hq
  · simpa [hq] using hr
  rcases hr with hr | hr
  · exact Or.inr (by simpa [hr] using hq)
  by_cases hsum : q + r = 0
  · exact Or.inl hsum
  · right
    have hmin : b ≤ min (padicValRat p q) (padicValRat p r) := le_min hq hr
    exact le_trans hmin (padicValRat.min_le_padicValRat_add hsum)

theorem primeValuationLowerBound_mul {p : ℕ} [Fact p.Prime]
    {b c : ℤ} {q r : ℚ}
    (hq : PrimeValuationLowerBound p b q)
    (hr : PrimeValuationLowerBound p c r) :
    PrimeValuationLowerBound p (b + c) (q * r) := by
  rcases hq with hq | hq
  · exact Or.inl (by simp [hq])
  rcases hr with hr | hr
  · exact Or.inl (by simp [hr])
  · by_cases hq0 : q = 0
    · exact Or.inl (by simp [hq0])
    · by_cases hr0 : r = 0
      · exact Or.inl (by simp [hr0])
      · right
        rw [padicValRat.mul hq0 hr0]
        omega

theorem primeValuationLowerBound_intCast {p : ℕ} [Fact p.Prime] (z : ℤ) :
    PrimeValuationLowerBound p 0 (z : ℚ) := by
  by_cases hz : z = 0
  · exact Or.inl (by simp [hz])
  · right
    rw [padicValRat.of_int]
    exact_mod_cast (Nat.zero_le (padicValInt p z))

theorem primeValuationLowerBound_sum {p : ℕ} [Fact p.Prime] {α : Type*}
    (s : Finset α) (f : α → ℚ) (b : ℤ)
    (hf : ∀ a ∈ s, PrimeValuationLowerBound p b (f a)) :
    PrimeValuationLowerBound p b (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simp [PrimeValuationLowerBound]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply primeValuationLowerBound_add
      · exact hf a (Finset.mem_insert_self a s)
      · apply ih
        intro x hx
        exact hf x (Finset.mem_insert_of_mem hx)

theorem primeValuationLowerBound_coeff_mul {p : ℕ} [Fact p.Prime]
    {f g : PowerSeries ℚ} {a b : ℤ}
    (hf : ∀ i : ℕ, PrimeValuationLowerBound p (a - (i : ℤ)) (PowerSeries.coeff i f))
    (hg : ∀ i : ℕ, PrimeValuationLowerBound p (b - (i : ℤ)) (PowerSeries.coeff i g))
    (n : ℕ) :
    PrimeValuationLowerBound p (a + b - (n : ℤ))
      (PowerSeries.coeff n (f * g)) := by
  classical
  rw [PowerSeries.coeff_mul]
  apply primeValuationLowerBound_sum
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  apply primeValuationLowerBound_mono
    (primeValuationLowerBound_mul (hf ij.1) (hg ij.2))
  omega

theorem primeValuationLowerBound_finset_prod_coeff {p : ℕ} [Fact p.Prime]
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → PowerSeries ℚ)
    (b : α → ℤ)
    (hf : ∀ a ∈ s, ∀ k : ℕ,
      PrimeValuationLowerBound p (b a - (k : ℤ)) (PowerSeries.coeff k (f a)))
    (n : ℕ) :
    PrimeValuationLowerBound p ((∑ a ∈ s, b a) - (n : ℤ))
      (PowerSeries.coeff n (∏ a ∈ s, f a)) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      by_cases hn : n = 0
      · subst n
        simp [PrimeValuationLowerBound]
      · left
        simp [PrimeValuationLowerBound, hn]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact primeValuationLowerBound_coeff_mul
        (fun k => hf a (Finset.mem_insert_self a s) k)
        (fun k => ih (fun x hx i => hf x (Finset.mem_insert_of_mem hx) i) k) n

theorem primeValuationLowerBound_C {p : ℕ} {b : ℤ} {q : ℚ}
    (h : PrimeValuationLowerBound p b q) (n : ℕ) :
    PrimeValuationLowerBound p (b - (n : ℤ))
      (PowerSeries.coeff n (PowerSeries.C q)) := by
  by_cases hn : n = 0
  · subst n
    simpa using h
  · left
    rw [PowerSeries.coeff_C, if_neg hn]

theorem primeValuationLowerBound_intLinear {p : ℕ} [Fact p.Prime]
    (ell n : ℕ) :
    PrimeValuationLowerBound p (-(n : ℤ))
      (PowerSeries.coeff n
        (PowerSeries.C (-(ell : ℚ)) + (PowerSeries.X : PowerSeries ℚ))) := by
  by_cases hn0 : n = 0
  · subst n
    simpa using
      primeValuationLowerBound_intCast (p := p) (-(ell : ℤ))
  · by_cases hn1 : n = 1
    · subst n
      have h := primeValuationLowerBound_mono
        (primeValuationLowerBound_intCast (p := p) (1 : ℤ))
        (show (-(1 : ℤ)) ≤ 0 by norm_num)
      have hcoeff : PowerSeries.coeff 1
          (PowerSeries.C (-(ell : ℚ)) + (PowerSeries.X : PowerSeries ℚ)) = 1 := by
        rw [map_add, PowerSeries.coeff_C_of_ne_zero (by norm_num),
          PowerSeries.coeff_one_X, zero_add]
      rw [hcoeff]
      simpa using h
    · left
      have hcoeff : PowerSeries.coeff n
          (PowerSeries.C (-(ell : ℚ)) + (PowerSeries.X : PowerSeries ℚ)) = 0 := by
        rw [map_add, PowerSeries.coeff_C_of_ne_zero hn0, PowerSeries.coeff_X,
          if_neg hn1]
        simp
      exact hcoeff

theorem padicValNat_factorial_eq_zero_of_lt {p k : ℕ} [Fact p.Prime]
    (hk : k < p) : padicValNat p k.factorial = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k + 1 < p := by omega
      have hnot : ¬ p ∣ k + 1 := by
        intro hdiv
        have hle : p ≤ k + 1 := Nat.le_of_dvd (by omega) hdiv
        omega
      rw [Nat.factorial_succ,
        padicValNat.mul (by omega) (Nat.factorial_ne_zero k),
        padicValNat.eq_zero_of_not_dvd hnot]
      rw [ih (by omega)]

theorem padicValNat_factorial_eq_div_of_lt_sq {p n : ℕ} [Fact p.Prime]
    (hn : n < p * p) :
    padicValNat p n.factorial = n / p := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hquot : n / p < p :=
    (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hn)
  calc
    padicValNat p n.factorial = padicValNat p (p * (n / p)).factorial :=
      (padicValNat_mul_div_factorial (p := p) n).symm
    _ = padicValNat p (n / p).factorial + n / p :=
      padicValNat_factorial_mul (p := p) (n / p)
    _ = n / p := by rw [padicValNat_factorial_eq_zero_of_lt hquot]; omega

theorem padicValNat_choose_eq_carry_of_lt_sq {p n k : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) (hn : n < p * p) :
    padicValNat p (Nat.choose n k) =
      n / p - k / p - (n - k) / p := by
  rw [Nat.choose_eq_factorial_div_factorial hkn,
    padicValNat.div_of_dvd (Nat.factorial_mul_factorial_dvd_factorial hkn),
    padicValNat.mul (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero (n - k)),
    padicValNat_factorial_eq_div_of_lt_sq hn,
    padicValNat_factorial_eq_div_of_lt_sq (by omega),
    padicValNat_factorial_eq_div_of_lt_sq (by omega)]
  omega

theorem padicValRat_int_abs_le_one_of_lt_sq {p n : ℕ} {e : ℤ}
    [Fact p.Prime] (hn : n < p * p) (he : e ≠ 0) (hlen : e.natAbs ≤ n) :
    padicValRat p (e : ℚ) ≤ 1 := by
  have hpos : 0 < e.natAbs := Int.natAbs_pos.mpr he
  have hnot : ¬p ^ 2 ∣ e.natAbs := by
    intro hdvd
    have hle : p ^ 2 ≤ e.natAbs := Nat.le_of_dvd hpos hdvd
    have hle' : p * p ≤ e.natAbs := by simpa [pow_two] using hle
    omega
  have hval : ¬2 ≤ padicValNat p e.natAbs := by
    intro hge
    have hdvd : p ^ 2 ∣ e.natAbs :=
      (padicValNat_dvd_iff_le (a := e.natAbs) (n := 2) (Nat.ne_of_gt hpos)).2 hge
    exact hnot hdvd
  rw [padicValRat.of_int, padicValInt]
  omega

theorem normalizedReciprocal_coeff_lower_of_bound {p bound k : ℕ} {e : ℤ}
    [Fact p.Prime] (hbound : bound < p * p) (he : e ≠ 0)
    (hlen : e.natAbs ≤ bound) :
    PrimeValuationLowerBound p (-(k : ℤ))
      (PowerSeries.coeff k (normalizedReciprocal e)) := by
  by_cases hzero : PowerSeries.coeff k (normalizedReciprocal e) = 0
  · exact Or.inl hzero
  · right
    have heQ : (e : ℚ) ≠ 0 := by exact_mod_cast he
    have heval := padicValRat_int_abs_le_one_of_lt_sq hbound he hlen
    have hbase : -1 ≤ padicValRat p (-1 / (e : ℚ)) := by
      rw [padicValRat.div (by norm_num) heQ]
      simp only [padicValRat.neg, padicValRat.one]
      omega
    have hmul := mul_le_mul_of_nonneg_left hbase (show 0 ≤ (k : ℤ) by positivity)
    simpa [normalizedReciprocal, PowerSeries.coeff_mk, padicValRat.pow] using hmul

theorem normalizedReciprocal_finsetProd_coeff_lower {p bound k : ℕ}
    [Fact p.Prime] {α : Type*} [DecidableEq α] (s : Finset α) (e : α → ℤ)
    (hbound : bound < p * p)
    (hne : ∀ a ∈ s, e a ≠ 0)
    (hlen : ∀ a ∈ s, (e a).natAbs ≤ bound) :
    PrimeValuationLowerBound p (-(k : ℤ))
      (PowerSeries.coeff k (∏ a ∈ s, normalizedReciprocal (e a))) := by
  simpa [Finset.sum_const_zero] using primeValuationLowerBound_finset_prod_coeff s
    (fun a => normalizedReciprocal (e a)) (fun _ => 0)
    (by
      intro a ha i
      simpa using normalizedReciprocal_coeff_lower_of_bound hbound
        (hne a ha) (hlen a ha)) k

theorem padicValNat_le_one_of_le_lt_sq {p n k : ℕ} [Fact p.Prime]
    (hk0 : k ≠ 0) (hkn : k ≤ n) (hn : n < p * p) :
    padicValNat p k ≤ 1 := by
  have hnot : ¬p ^ 2 ∣ k := by
    intro hdvd
    have hle : p ^ 2 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd
    have hle' : p * p ≤ k := by simpa [pow_two] using hle
    exact (Nat.not_le_of_gt hn) (le_trans hle' hkn)
  have hval : ¬2 ≤ padicValNat p k := by
    intro hge
    exact hnot ((padicValNat_dvd_iff_le (a := k) (n := 2) hk0).2 hge)
  omega

theorem padicValNat_intervalLcm_eq_one {p n : ℕ} [Fact p.Prime]
    (hp_le : p ≤ n) (hn : n < p * p) :
    padicValNat p (intervalLcm n) = 1 := by
  classical
  let s : Finset ℕ := Finset.Icc 1 n
  have hfac : (intervalLcm n).factorization p =
      s.sup fun k => k.factorization p := by
    change ((Finset.Icc 1 n).lcm id).factorization p =
      (Finset.Icc 1 n).sup fun k => k.factorization p
    exact Finset.factorization_lcm (fun k hk => by
      have hk' := Finset.mem_Icc.mp hk
      exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk'.1)) p
  have hfacVal : (intervalLcm n).factorization p =
      s.sup fun k => padicValNat p k := by
    rw [hfac]
    apply Finset.sup_congr rfl
    intro k hk
    by_cases hk : k = 0
    · simp [hk]
    · exact Nat.factorization_def k Fact.out
  have hupper : s.sup (fun k => padicValNat p k) ≤ 1 := by
    apply Finset.sup_le
    intro k hk
    have hk' := Finset.mem_Icc.mp (show k ∈ Finset.Icc 1 n from by simpa [s] using hk)
    exact padicValNat_le_one_of_le_lt_sq (by omega) hk'.2 hn
  have hpPrime : Nat.Prime p := Fact.out
  have hpMem : p ∈ s := by
    exact Finset.mem_Icc.mpr ⟨hpPrime.one_le, hp_le⟩
  have hlower : 1 ≤ s.sup (fun k => padicValNat p k) := by
    exact Finset.le_sup_of_le hpMem (by simp)
  rw [← Nat.factorization_def (intervalLcm n) Fact.out, hfacVal]
  exact le_antisymm hupper hlower

theorem padicValRat_intervalLcm_eq_one {p n : ℕ} [Fact p.Prime]
    (hp_le : p ≤ n) (hn : n < p * p) :
    padicValRat p (intervalLcm n : ℚ) = 1 := by
  rw [padicValRat.of_nat, padicValNat_intervalLcm_eq_one hp_le hn]
  norm_num

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem binomialWeight_padicVal_eq_intervalCarry {p : ℕ} [Fact p.Prime]
    (a : Fin M) {ell : ℕ} (hmem : ell ∈ P.interval a)
    (hn : P.n < p * p) :
    padicValRat p (P.binomialWeight a ell) = P.intervalCarry a p ell := by
  have hmem' := (P.interval_mem_iff a ell).mp hmem
  let t := ell - P.left a
  let u := P.right a - ell
  have htu : t + u = P.length a := by
    dsimp [t, u]
    rw [P.length_eq]
    omega
  have ht : t ≤ P.length a := by omega
  have hlen : P.length a < p * p := by
    have hle : P.length a ≤ P.n := by
      simpa [ActualIntervals.length] using
        (Nat.sub_le P.n (2 * P.left a))
    exact lt_of_le_of_lt hle hn
  have hlenSplit : P.length a - t = u := by
    dsimp [t, u]
    rw [P.length_eq]
    omega
  have hpPrime : Nat.Prime p := Fact.out
  have hfloorSum : t / p + u / p ≤ P.length a / p := by
    have hcarry := P.intervalCarry_zero_or_one a
      hpPrime.pos (le_trans hmem'.2 (P.right_le_n a))
    have hcast : P.intervalCarry a p ell =
        (P.length a / p : ℤ) - (t / p : ℤ) - (u / p : ℤ) := by
      unfold ActualIntervals.intervalCarry
      dsimp [t, u]
      rw [← Int.natCast_sub hmem'.1, ← Int.natCast_sub hmem'.2,
        ← Int.natCast_div, ← Int.natCast_div, ← Int.natCast_div]
    rcases hcarry with h0 | h1
    · rw [hcast] at h0
      omega
    · rw [hcast] at h1
      omega
  have htdiv : t / p ≤ P.length a / p := le_trans (Nat.le_add_right _ _) hfloorSum
  have hudiv : u / p ≤ P.length a / p - t / p := by omega
  have hsubcast :
      ((P.length a / p - t / p - u / p : ℕ) : ℤ) =
        ((P.length a / p : ℕ) : ℤ) - ((t / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) := by
    rw [Int.natCast_sub hudiv, Int.natCast_sub htdiv]
  have hcarryCast : P.intervalCarry a p ell =
      ((P.length a / p - t / p - u / p : ℕ) : ℤ) := by
    have hcast : P.intervalCarry a p ell =
        ((P.length a / p : ℕ) : ℤ) - ((t / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) := by
      unfold ActualIntervals.intervalCarry
      dsimp [t, u]
      rw [← Int.natCast_sub hmem'.1, ← Int.natCast_sub hmem'.2,
        ← Int.natCast_div, ← Int.natCast_div, ← Int.natCast_div]
    rw [hcast, hsubcast]
  have hchoose := padicValNat_choose_eq_carry_of_lt_sq ht hlen
  have hchooseNZ : ((Nat.choose (P.length a) t : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero ht)
  have hsignNZ : (((-1 : ℤ) ^ t : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero t (by norm_num : (-1 : ℤ) ≠ 0))
  have hsignVal : padicValRat p (((-1 : ℤ) ^ t : ℤ) : ℚ) = 0 := by
    rw [padicValRat.of_int]
    simp [padicValInt]
  have hchooseVal :
      padicValRat p ((Nat.choose (P.length a) t : ℤ) : ℚ) =
        padicValNat p (Nat.choose (P.length a) t) := by
    rw [padicValRat.of_int]
    simp [padicValInt]
  have hweight : P.binomialWeight a ell =
      (((-1 : ℤ) ^ t : ℤ) : ℚ) * ((Nat.choose (P.length a) t : ℤ) : ℚ) := by
    simp [ActualIntervals.binomialWeight, t]
  have hchoose' := hchoose
  rw [hlenSplit] at hchoose'
  have hchooseInt :
      (padicValNat p (Nat.choose (P.length a) t) : ℤ) =
        ((P.length a / p : ℕ) : ℤ) - ((t / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) := by
    have hcast := congrArg (fun v : ℕ => (v : ℤ)) hchoose'
    rw [Int.natCast_sub hudiv, Int.natCast_sub htdiv] at hcast
    exact hcast
  rw [hweight, padicValRat.mul hsignNZ hchooseNZ, hsignVal, hchooseVal]
  simp only [zero_add]
  calc
    (padicValNat p (Nat.choose (P.length a) t) : ℤ) =
        ((P.length a / p : ℕ) : ℤ) - ((t / p : ℕ) : ℤ) - ((u / p : ℕ) : ℤ) := hchooseInt
    _ = ((P.length a / p - t / p - u / p : ℕ) : ℤ) := hsubcast.symm
    _ = P.intervalCarry a p ell := hcarryCast.symm

end ActualIntervals

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem intervalDistanceProduct_before (a : Fin M) {ell : ℕ}
    (hell : ell < P.left a) :
    (∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)) =
      (Nat.ascFactorial (P.left a - ell) (P.length a + 1) : ℚ) := by
  classical
  have hcount : P.right a + 1 - P.left a = P.length a + 1 := by
    have hleftRight := P.left_le_right a
    rw [P.length_eq]
    omega
  have hIcc : Finset.Icc (P.left a) (P.right a) =
      Finset.Ico (P.left a) (P.right a + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [ActualIntervals.interval, hIcc, Finset.prod_Ico_eq_prod_range, hcount]
  calc
    (∏ k ∈ Finset.range (P.length a + 1),
        (((P.left a + k : ℕ) : ℤ) - (ell : ℤ) : ℚ)) =
      ∏ k ∈ Finset.range (P.length a + 1),
        (((P.left a - ell + k : ℕ) : ℚ)) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hle : ell ≤ P.left a + k := by omega
          have hnat : P.left a + k - ell = P.left a - ell + k := by omega
          have hInt :
              ((P.left a + k : ℕ) : ℤ) - (ell : ℤ) =
                ((P.left a - ell + k : ℕ) : ℤ) := by
            rw [← Int.natCast_sub hle]
            exact_mod_cast hnat
          exact_mod_cast hInt
    _ = (Nat.ascFactorial (P.left a - ell) (P.length a + 1) : ℚ) := by
          rw [Nat.ascFactorial_eq_prod_range]
          norm_cast

theorem intervalDistanceProduct_after (a : Fin M) {ell : ℕ}
    (hell : P.right a < ell) :
    (∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)) =
      (-1 : ℚ) ^ (P.length a + 1) *
        (Nat.ascFactorial (ell - P.right a) (P.length a + 1) : ℚ) := by
  classical
  let d := P.length a + 1
  let s := ell - P.right a
  have hcount : P.right a + 1 - P.left a = d := by
    have hleftRight := P.left_le_right a
    dsimp [d]
    rw [P.length_eq]
    omega
  have hIcc : Finset.Icc (P.left a) (P.right a) =
      Finset.Ico (P.left a) (P.right a + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [ActualIntervals.interval, hIcc, Finset.prod_Ico_eq_prod_range, hcount]
  calc
    (∏ k ∈ Finset.range d,
        (((P.left a + k : ℕ) : ℤ) - (ell : ℤ) : ℚ)) =
      ∏ k ∈ Finset.range d,
        -(((s + (d - 1 - k) : ℕ) : ℚ)) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hklt : k < d := Finset.mem_range.mp hk
          have hsum : P.left a + k + (s + (d - 1 - k)) = ell := by
            have hleftRight := P.left_le_right a
            dsimp [s, d]
            rw [P.length_eq]
            omega
          have hnat : ell - (P.left a + k) = s + (d - 1 - k) := by omega
          have hle : P.left a + k ≤ ell := by omega
          have hterm :
              (P.left a + k : ℤ) - (ell : ℤ) =
                -((s + (d - 1 - k) : ℕ) : ℤ) := by
            have hterm' :
                (ell : ℤ) - ((P.left a + k : ℕ) : ℤ) =
                  ((s + (d - 1 - k) : ℕ) : ℤ) := by
              rw [← Int.natCast_sub hle]
              exact_mod_cast hnat
            omega
          exact_mod_cast hterm
    _ = (-1 : ℚ) ^ d *
        ∏ k ∈ Finset.range d, (((s + (d - 1 - k) : ℕ) : ℚ)) := by
          rw [Finset.prod_neg, Finset.card_range]
    _ = (-1 : ℚ) ^ d *
        ∏ k ∈ Finset.range d, (((s + k : ℕ) : ℚ)) := by
          congr 1
          exact Finset.prod_range_reflect (fun k => (((s + k : ℕ) : ℚ))) d
    _ = (-1 : ℚ) ^ d * (Nat.ascFactorial s d : ℚ) := by
          rw [Nat.ascFactorial_eq_prod_range]
          norm_cast

end ActualIntervals

theorem intNegNatDiv_eq {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    (-(s : ℤ)) / (p : ℤ) = -(((s - 1) / p : ℕ) : ℤ) - 1 := by
  change Int.ediv (-(s : ℤ)) (p : ℤ) = _
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp
  have hsOne : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hdiv :
      Int.ediv (-(s : ℤ)) (p : ℤ) =
        -((((s - 1 : ℕ) : ℤ) / (p : ℤ)) + 1) := by
    have h := Int.ediv_of_neg_of_pos
      (a := -(s : ℤ)) (b := (p : ℤ)) (by omega) hpZ
    have hnat : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 :=
      Int.natCast_sub hsOne
    simpa [hnat] using h
  calc
    Int.ediv (-(s : ℤ)) (p : ℤ) =
        -((((s - 1 : ℕ) : ℤ) / (p : ℤ)) + 1) := hdiv
    _ = -(((s - 1) / p : ℕ) : ℤ) - 1 := by
      rw [← Int.natCast_div]
      ring

theorem padicValNat_ascFactorial_eq_div_sub_of_lt_sq {p s d : ℕ}
    [Fact p.Prime] (hs : 0 < s) (hsd : s + d < p * p)
    (hsminus : s - 1 < p * p) :
    padicValNat p (Nat.ascFactorial s (d + 1)) =
      (s + d) / p - (s - 1) / p := by
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs)
  have hshift : s - 1 + 1 = s := Nat.sub_add_cancel hs1
  have hprod :
      (s - 1).factorial * Nat.ascFactorial s (d + 1) = (s + d).factorial := by
    calc
      _ = (s - 1).factorial * Nat.ascFactorial ((s - 1) + 1) (d + 1) := by
        rw [hshift]
      _ = ((s - 1) + (d + 1)).factorial :=
        Nat.factorial_mul_ascFactorial (s - 1) (d + 1)
      _ = (s + d).factorial := by congr 1 <;> omega
  have hAscPos : 0 < Nat.ascFactorial s (d + 1) := by
    rw [← hshift]
    exact Nat.ascFactorial_pos (s - 1) (d + 1)
  have hval := congrArg (padicValNat p) hprod
  rw [padicValNat.mul (Nat.factorial_ne_zero (s - 1)) (Nat.ne_of_gt hAscPos),
    padicValNat_factorial_eq_div_of_lt_sq hsd,
    padicValNat_factorial_eq_div_of_lt_sq hsminus] at hval
  omega

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem intervalCarry_before_eq (a : Fin M) {p ell : ℕ}
    (hp : 0 < p) (hleft : ell < P.left a) :
    P.intervalCarry a p ell =
      ((P.length a / p : ℕ) : ℤ) +
        (((P.left a - ell - 1) / p : ℕ) : ℤ) + 1 -
          (((P.right a - ell) / p : ℕ) : ℤ) := by
  have hleftRight := P.left_le_right a
  have hs : 0 < P.left a - ell := by omega
  have hleftCast : ((P.left a - ell : ℕ) : ℤ) =
      (P.left a : ℤ) - (ell : ℤ) := Int.natCast_sub (by omega)
  have hrightCast : ((P.right a - ell : ℕ) : ℤ) =
      (P.right a : ℤ) - (ell : ℤ) := Int.natCast_sub (by omega)
  unfold intervalCarry
  rw [show (ell : ℤ) - (P.left a : ℤ) =
      -((P.left a - ell : ℕ) : ℤ) by omega,
    ← hrightCast, intNegNatDiv_eq hp hs,
    ← Int.natCast_div, ← Int.natCast_div]
  ring

theorem intervalCarry_after_eq (a : Fin M) {p ell : ℕ}
    (hp : 0 < p) (hright : P.right a < ell) :
    P.intervalCarry a p ell =
      ((P.length a / p : ℕ) : ℤ) -
        (((ell - P.left a) / p : ℕ) : ℤ) +
          (((ell - P.right a - 1) / p : ℕ) : ℤ) + 1 := by
  have hleftRight := P.left_le_right a
  have hs : 0 < ell - P.right a := by omega
  have hrightCast : ((ell - P.right a : ℕ) : ℤ) =
      (ell : ℤ) - (P.right a : ℤ) := Int.natCast_sub (by omega)
  have hleftCast : ((ell - P.left a : ℕ) : ℤ) =
      (ell : ℤ) - (P.left a : ℤ) := Int.natCast_sub (by omega)
  unfold intervalCarry
  rw [← hleftCast,
    show (P.right a : ℤ) - (ell : ℤ) =
      -((ell - P.right a : ℕ) : ℤ) by omega,
    intNegNatDiv_eq hp hs, ← Int.natCast_div, ← Int.natCast_div]
  ring

/-- The constant in the reciprocal-product form of an external regular local
factor. -/
noncomputable def regularLocalScalar (a : Fin M) (ell : ℕ) : ℚ :=
  (Nat.factorial (P.length a) : ℚ) /
    ∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)

theorem normalizedReciprocal_mul_linear (e : ℤ) (he : e ≠ 0) :
    normalizedReciprocal e *
      (PowerSeries.C (e : ℚ) + PowerSeries.X) = PowerSeries.C (e : ℚ) := by
  have heQ : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have hC : PowerSeries.C (e : ℚ) * PowerSeries.C (1 / (e : ℚ)) = 1 := by
    rw [← map_mul]
    simp [heQ]
  have hCreg : PowerSeries.C (e : ℚ) * regularReciprocal e =
      normalizedReciprocal e := by
    rw [regularReciprocal, ← mul_assoc, hC]
    simp
  calc
    _ = PowerSeries.C (e : ℚ) *
          ((PowerSeries.C (e : ℚ) + PowerSeries.X) * regularReciprocal e) := by
            rw [← hCreg]
            ring
    _ = PowerSeries.C (e : ℚ) := by
          rw [regularReciprocal_identity e he]
          simp

theorem regularLocalFactor_eq_scalar_mul_normalizedProduct (a : Fin M) (ell : ℕ)
    (hmem : ell ∉ P.interval a) :
    P.regularLocalFactor a ell =
      PowerSeries.C (P.regularLocalScalar a ell) *
        ∏ r ∈ P.interval a, normalizedReciprocal ((r : ℤ) - (ell : ℤ)) := by
  classical
  let e : ℕ → ℤ := fun r => (r : ℤ) - (ell : ℤ)
  let E : ℚ := ∏ r ∈ P.interval a, (e r : ℚ)
  let D : PowerSeries ℚ :=
    ∏ r ∈ P.interval a, (PowerSeries.C (e r : ℚ) + PowerSeries.X)
  let G : PowerSeries ℚ := ∏ r ∈ P.interval a, normalizedReciprocal (e r)
  have heInt : ∀ r ∈ P.interval a, e r ≠ 0 := by
    intro r hr hz
    apply hmem
    have hcast : (r : ℤ) = (ell : ℤ) := sub_eq_zero.mp (by simpa [e] using hz)
    have hrEq : r = ell := Int.ofNat.inj hcast
    simpa [hrEq] using hr
  have heQ : ∀ r ∈ P.interval a, (e r : ℚ) ≠ 0 := by
    intro r hr
    exact_mod_cast heInt r hr
  have hE0 : E ≠ 0 := by
    dsimp [E]
    apply Finset.prod_ne_zero_iff.mpr
    exact heQ
  have hlinear : ∀ r ∈ P.interval a,
      (PowerSeries.C (e r : ℚ) + PowerSeries.X) ≠ 0 := by
    intro r hr hz
    have hc := congrArg (PowerSeries.coeff 0) hz
    apply heQ r hr
    simpa using hc
  have hD0 : D ≠ 0 := by
    dsimp [D]
    apply Finset.prod_ne_zero_iff.mpr
    exact hlinear
  have hfactor : ∀ r ∈ P.interval a,
      normalizedReciprocal (e r) *
        (PowerSeries.C (e r : ℚ) + PowerSeries.X) = PowerSeries.C (e r : ℚ) := by
    intro r hr
    exact normalizedReciprocal_mul_linear (e r) (heInt r hr)
  have hGD : G * D = PowerSeries.C E := by
    calc
      _ = ∏ r ∈ P.interval a,
            (normalizedReciprocal (e r) *
              (PowerSeries.C (e r : ℚ) + PowerSeries.X)) := by
              rw [← Finset.prod_mul_distrib]
      _ = ∏ r ∈ P.interval a, PowerSeries.C (e r : ℚ) := by
              apply Finset.prod_congr rfl
              intro r hr
              exact hfactor r hr
      _ = PowerSeries.C E := by
              dsimp [E]
              induction P.interval a using Finset.induction_on with
              | empty => simp
              | @insert r s hr ih =>
                  rw [Finset.prod_insert hr, Finset.prod_insert hr, ih, ← map_mul]
  have hscalarE : P.regularLocalScalar a ell * E =
      (Nat.factorial (P.length a) : ℚ) := by
    have hdenom :
        (∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)) = E := by
      simp [E, e, Int.cast_sub]
    dsimp [regularLocalScalar]
    rw [hdenom]
    field_simp [hE0]
  have hRegular := P.regularLocalFactor_mul_localDenominator a ell hmem
  have hCandidate :
      (PowerSeries.C (P.regularLocalScalar a ell) * G) * D =
        PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by
    calc
      _ = PowerSeries.C (P.regularLocalScalar a ell) * (G * D) := by ring
      _ = PowerSeries.C (P.regularLocalScalar a ell) * PowerSeries.C E := by rw [hGD]
      _ = PowerSeries.C (P.regularLocalScalar a ell * E) := by rw [← map_mul]
      _ = PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by rw [hscalarE]
  apply mul_right_cancel₀ hD0
  calc
    P.regularLocalFactor a ell * D =
        PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by simpa [D, e] using hRegular
    _ = (PowerSeries.C (P.regularLocalScalar a ell) * G) * D := hCandidate.symm

theorem regularLocalScalar_padicVal_eq_carry_sub_one (a : Fin M)
    {p ell : ℕ} [Fact p.Prime] (hell : ell ≤ P.n)
    (hn : P.n < p * p) (hmem : ell ∉ P.interval a) :
    padicValRat p (P.regularLocalScalar a ell) =
      P.intervalCarry a p ell - 1 := by
  have hp := (Fact.out : Nat.Prime p).pos
  have hleftRight := P.left_le_right a
  by_cases hleft : ell < P.left a
  · let s := P.left a - ell
    let d := P.length a
    have hs : 0 < s := by dsimp [s]; omega
    have hsd : s + d = P.right a - ell := by
      dsimp [s, d]
      rw [P.length_eq]
      omega
    have hsdLe : s + d ≤ P.n := by
      rw [hsd]
      exact Nat.le_trans (Nat.sub_le _ _) (P.right_le_n a)
    have hsdSq : s + d < p * p := lt_of_le_of_lt hsdLe hn
    have hsminusSq : s - 1 < p * p := by omega
    have hdist :
        (∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)) =
          (Nat.ascFactorial s (d + 1) : ℚ) := by
      simpa [s, d] using P.intervalDistanceProduct_before a hleft
    have hAscPos : 0 < Nat.ascFactorial s (d + 1) := by
      have hs1 : 1 ≤ s := by omega
      rw [← Nat.sub_add_cancel hs1]
      exact Nat.ascFactorial_pos (s - 1) (d + 1)
    have hdenNZ :
        (∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)) ≠ 0 := by
      rw [hdist]
      exact_mod_cast (Nat.ne_of_gt hAscPos)
    have hdenVal :
        padicValRat p (∏ r ∈ P.interval a,
          (((r : ℤ) - (ell : ℤ)) : ℚ)) =
          (((s + d) / p : ℕ) : ℤ) - (((s - 1) / p : ℕ) : ℤ) := by
      rw [hdist, padicValRat.of_nat]
      have hdivLe : (s - 1) / p ≤ (s + d) / p :=
        Nat.div_le_div_right (by omega)
      rw [← Int.natCast_sub hdivLe]
      exact_mod_cast
        (padicValNat_ascFactorial_eq_div_sub_of_lt_sq hs hsdSq hsminusSq)
    have hnumNZ : (Nat.factorial d : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero d
    have hnumVal :
        padicValRat p (Nat.factorial d : ℚ) = ((d / p : ℕ) : ℤ) := by
      rw [padicValRat.of_nat, padicValNat_factorial_eq_div_of_lt_sq (by
        exact lt_of_le_of_lt (by dsimp [d]; exact Nat.sub_le _ _) hn)]
    have hscalarVal :
        padicValRat p (P.regularLocalScalar a ell) =
          ((d / p : ℕ) : ℤ) - (((s + d) / p : ℕ) : ℤ) +
            (((s - 1) / p : ℕ) : ℤ) := by
      rw [regularLocalScalar, padicValRat.div hnumNZ hdenNZ, hnumVal, hdenVal]
      ring
    have hleftDiff : P.left a - ell - 1 = s - 1 := by dsimp [s]
    have hcarry : P.intervalCarry a p ell - 1 =
        ((d / p : ℕ) : ℤ) - (((s + d) / p : ℕ) : ℤ) +
          (((s - 1) / p : ℕ) : ℤ) := by
      rw [P.intervalCarry_before_eq a hp hleft, hleftDiff, ← hsd]
      dsimp [d]
      ring
    rw [hscalarVal, hcarry]
  · have hleftLe : P.left a ≤ ell := Nat.le_of_not_gt hleft
    have hright : P.right a < ell := by
      by_contra h
      have hEllRight : ell ≤ P.right a := Nat.le_of_not_gt h
      exact hmem ((P.interval_mem_iff a ell).2 ⟨hleftLe, hEllRight⟩)
    let s := ell - P.right a
    let d := P.length a
    have hs : 0 < s := by dsimp [s]; omega
    have hsd : s + d = ell - P.left a := by
      dsimp [s, d]
      rw [P.length_eq]
      omega
    have hsdLe : s + d ≤ P.n := by
      rw [hsd]
      exact Nat.le_trans (Nat.sub_le _ _) hell
    have hsdSq : s + d < p * p := lt_of_le_of_lt hsdLe hn
    have hsminusSq : s - 1 < p * p := by omega
    have hdist :
        (∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)) =
          (-1 : ℚ) ^ (d + 1) *
            (Nat.ascFactorial s (d + 1) : ℚ) := by
      simpa [s, d] using P.intervalDistanceProduct_after a hright
    have hAscPos : 0 < Nat.ascFactorial s (d + 1) := by
      have hs1 : 1 ≤ s := by omega
      rw [← Nat.sub_add_cancel hs1]
      exact Nat.ascFactorial_pos (s - 1) (d + 1)
    have hsignNZ : (-1 : ℚ) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hAscNZ : (Nat.ascFactorial s (d + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hAscPos)
    have hdenNZ :
        (∏ r ∈ P.interval a, (((r : ℤ) - (ell : ℤ)) : ℚ)) ≠ 0 := by
      rw [hdist]
      exact mul_ne_zero hsignNZ hAscNZ
    have hdenVal :
        padicValRat p (∏ r ∈ P.interval a,
          (((r : ℤ) - (ell : ℤ)) : ℚ)) =
          (((s + d) / p : ℕ) : ℤ) - (((s - 1) / p : ℕ) : ℤ) := by
      rw [hdist, padicValRat.mul hsignNZ hAscNZ]
      have hsignVal : padicValRat p ((-1 : ℚ) ^ (d + 1)) = 0 := by
        simp [padicValRat.pow, padicValRat.neg, padicValRat.one]
      rw [hsignVal, zero_add, padicValRat.of_nat]
      have hdivLe : (s - 1) / p ≤ (s + d) / p :=
        Nat.div_le_div_right (by omega)
      rw [← Int.natCast_sub hdivLe]
      exact_mod_cast
        (padicValNat_ascFactorial_eq_div_sub_of_lt_sq hs hsdSq hsminusSq)
    have hnumNZ : (Nat.factorial d : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero d
    have hnumVal :
        padicValRat p (Nat.factorial d : ℚ) = ((d / p : ℕ) : ℤ) := by
      rw [padicValRat.of_nat, padicValNat_factorial_eq_div_of_lt_sq (by
        exact lt_of_le_of_lt (by dsimp [d]; exact Nat.sub_le _ _) hn)]
    have hscalarVal :
        padicValRat p (P.regularLocalScalar a ell) =
          ((d / p : ℕ) : ℤ) - (((s + d) / p : ℕ) : ℤ) +
            (((s - 1) / p : ℕ) : ℤ) := by
      rw [regularLocalScalar, padicValRat.div hnumNZ hdenNZ, hnumVal, hdenVal]
      ring
    have hleftDiff : ell - P.right a - 1 = s - 1 := by dsimp [s]
    have hcarry : P.intervalCarry a p ell - 1 =
        ((d / p : ℕ) : ℤ) - (((s + d) / p : ℕ) : ℤ) +
          (((s - 1) / p : ℕ) : ℤ) := by
      rw [P.intervalCarry_after_eq a hp hright, hsd, hleftDiff]
      dsimp [d]
      ring
    rw [hscalarVal, hcarry]

theorem intervalDistance_ne_zero (a : Fin M) {ell r : ℕ}
    (hne : r ≠ ell) (hr : r ∈ P.interval a) :
    (r : ℤ) - (ell : ℤ) ≠ 0 := by
  intro h
  have hcast : (r : ℤ) = (ell : ℤ) := sub_eq_zero.mp h
  have heq : r = ell := Int.ofNat.inj hcast
  exact hne heq

theorem intervalDistance_natAbs_le_n (a : Fin M) {ell r : ℕ}
    (hell : ell ≤ P.n) (hr : r ∈ P.interval a) :
    ((r : ℤ) - (ell : ℤ)).natAbs ≤ P.n := by
  have hrBounds := (P.interval_mem_iff a r).mp hr
  have hrn : r ≤ P.n := le_trans hrBounds.2 (P.right_le_n a)
  by_cases hle : r ≤ ell
  · have hcast : (r : ℤ) - (ell : ℤ) = -((ell - r : ℕ) : ℤ) := by
      rw [Int.natCast_sub hle]
      ring
    rw [hcast]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    omega
  · have hle' : ell ≤ r := by omega
    have hcast : (r : ℤ) - (ell : ℤ) = ((r - ell : ℕ) : ℤ) := by
      rw [← Int.natCast_sub hle']
    rw [hcast, Int.natAbs_natCast]
    omega

theorem poleLocalFactor_coeff_lower {p ell u : ℕ} [Fact p.Prime]
    (a : Fin M) (hmem : ell ∈ P.interval a) (hn : P.n < p * p) :
    PrimeValuationLowerBound p
      (((P.intervalCarryNat a p ell : ℕ) : ℤ) - (u : ℤ))
      (PowerSeries.coeff u (P.poleLocalFactor a ell)) := by
  have hp := (Fact.out : Nat.Prime p).pos
  have hell : ell ≤ P.n :=
    le_trans ((P.interval_mem_iff a ell).mp hmem).2 (P.right_le_n a)
  have hcarryNat :
      ((P.intervalCarryNat a p ell : ℕ) : ℤ) = P.intervalCarry a p ell := by
    rcases P.intervalCarry_zero_or_one a hp hell with hzero | hone
    · simp [ActualIntervals.intervalCarryNat, hzero]
    · simp [ActualIntervals.intervalCarryNat, hone]
  have hconstant :
      PrimeValuationLowerBound p
        ((P.intervalCarryNat a p ell : ℕ) : ℤ) (P.binomialWeight a ell) := by
    right
    rw [P.binomialWeight_padicVal_eq_intervalCarry a hmem hn, ← hcarryNat]
  let s := Finset.erase (P.interval a) ell
  let e : ℕ → ℤ := fun r => (r : ℤ) - (ell : ℤ)
  have hprod : ∀ k : ℕ,
      PrimeValuationLowerBound p (0 - (k : ℤ))
        (PowerSeries.coeff k (∏ r ∈ s, normalizedReciprocal (e r))) := by
    intro k
    simpa using normalizedReciprocal_finsetProd_coeff_lower (k := k) s e hn
      (by
        intro r hr
        have hr' := Finset.mem_erase.mp hr
        exact P.intervalDistance_ne_zero a hr'.1 hr'.2)
      (by
        intro r hr
        have hr' := Finset.mem_erase.mp hr
        exact P.intervalDistance_natAbs_le_n a hell hr'.2)
  have hmul := primeValuationLowerBound_coeff_mul
    (fun k => primeValuationLowerBound_C hconstant k) hprod u
  simpa [ActualIntervals.poleLocalFactor, s, e] using hmul

theorem regularLocalFactor_coeff_lower {p ell u : ℕ} [Fact p.Prime]
    (a : Fin M) (hell : ell ≤ P.n) (hmem : ell ∉ P.interval a)
    (hn : P.n < p * p) :
    PrimeValuationLowerBound p
      (((P.intervalCarryNat a p ell : ℕ) : ℤ) - 1 - (u : ℤ))
      (PowerSeries.coeff u (P.regularLocalFactor a ell)) := by
  have hp := (Fact.out : Nat.Prime p).pos
  have hcarryNat :
      ((P.intervalCarryNat a p ell : ℕ) : ℤ) = P.intervalCarry a p ell := by
    rcases P.intervalCarry_zero_or_one a hp hell with hzero | hone
    · simp [ActualIntervals.intervalCarryNat, hzero]
    · simp [ActualIntervals.intervalCarryNat, hone]
  have hscalar : PrimeValuationLowerBound p
      (((P.intervalCarryNat a p ell : ℕ) : ℤ) - 1)
      (P.regularLocalScalar a ell) := by
    right
    rw [P.regularLocalScalar_padicVal_eq_carry_sub_one a hell hn hmem,
      ← hcarryNat]
  let s := P.interval a
  let e : ℕ → ℤ := fun r => (r : ℤ) - (ell : ℤ)
  have hprod : ∀ k : ℕ,
      PrimeValuationLowerBound p (0 - (k : ℤ))
        (PowerSeries.coeff k (∏ r ∈ s, normalizedReciprocal (e r))) := by
    intro k
    simpa using normalizedReciprocal_finsetProd_coeff_lower (k := k) s e hn
      (by
        intro r hr
        have hrne : r ≠ ell := by
          intro heq
          apply hmem
          simpa [heq] using hr
        exact P.intervalDistance_ne_zero a hrne hr)
      (by
        intro r hr
        exact P.intervalDistance_natAbs_le_n a hell hr)
  rw [P.regularLocalFactor_eq_scalar_mul_normalizedProduct a ell hmem]
  have hmul := primeValuationLowerBound_coeff_mul
    (fun k => primeValuationLowerBound_C hscalar k) hprod u
  simpa [s, e, sub_eq_add_neg, add_assoc] using hmul

end ActualIntervals

theorem normalizedReciprocal_coeff_lower {p n : ℕ} {e : ℤ} [Fact p.Prime]
    (hn : n < p * p) (he : e ≠ 0) (hlen : e.natAbs ≤ n) :
    PrimeValuationLowerBound p (-(n : ℤ))
      (PowerSeries.coeff n (normalizedReciprocal e)) := by
  by_cases hzero : PowerSeries.coeff n (normalizedReciprocal e) = 0
  · exact Or.inl hzero
  · right
    have heQ : (e : ℚ) ≠ 0 := by exact_mod_cast he
    have heval := padicValRat_int_abs_le_one_of_lt_sq hn he hlen
    have hbase : -1 ≤ padicValRat p (-1 / (e : ℚ)) := by
      rw [padicValRat.div (by norm_num) heQ]
      simp only [padicValRat.neg, padicValRat.one]
      omega
    have hmul := mul_le_mul_of_nonneg_left hbase (show 0 ≤ (n : ℤ) by positivity)
    simpa [normalizedReciprocal, PowerSeries.coeff_mk, padicValRat.pow] using hmul

end OddPiPowers

end
