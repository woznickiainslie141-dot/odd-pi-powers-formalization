module

public import OddPiPowers.Construction.LocalDenominators
public import OddPiPowers.Construction.ConfluentJets
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.Ring

/-! The finite interval data and local coefficient presentation of the
manuscript's auxiliary polynomials. -/

@[expose] public section

namespace OddPiPowers

open Polynomial
open scoped PowerSeries BigOperators

/-- A nested family of the actual integer intervals used in the construction.
The left endpoints are nondecreasing and lie in the left half of `[0,n]`. -/
structure ActualIntervals (M : ℕ) where
  n : ℕ
  left : Fin M → ℕ
  left_mono : Monotone left
  left_bound : ∀ a, 2 * left a ≤ n

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

def right (a : Fin M) : ℕ := P.n - P.left a

def length (a : Fin M) : ℕ := P.n - 2 * P.left a

def interval (a : Fin M) : Finset ℕ := Finset.Icc (P.left a) (P.right a)

/-- The signed binomial residue weight at an interval endpoint. -/
noncomputable def binomialWeight (a : Fin M) (r : ℕ) : ℚ :=
  (((-1 : ℤ) ^ (r - P.left a) *
    (Nat.choose (P.length a) (r - P.left a) : ℤ)) : ℚ)

def multiplicity (ell : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin M => ell ∈ P.interval a).card

/-- The total number of pole occurrences in the finite denominator. -/
def totalMultiplicity : ℕ :=
  ∑ ell ∈ Finset.range (P.n + 1), P.multiplicity ell

def poleIndices (ell : ℕ) : Finset (Fin M) :=
  Finset.univ.filter fun a => ell ∈ P.interval a

def regularIndices (ell : ℕ) : Finset (Fin M) :=
  Finset.univ.filter fun a => ell ∉ P.interval a

/-- Product of the actual interval factors, before the local expansion. -/
noncomputable def denominator : Polynomial ℚ :=
  ∏ a : Fin M, ∏ r ∈ P.interval a, (X + C (r : ℚ))

theorem left_le_right (a : Fin M) : P.left a ≤ P.right a := by
  have h := P.left_bound a
  simp only [right]
  omega

theorem right_le_n (a : Fin M) : P.right a ≤ P.n := by
  simp [right]

theorem length_eq (a : Fin M) : P.length a = P.right a - P.left a := by
  simp only [length, right]
  omega

theorem interval_mem_iff (a : Fin M) (ell : ℕ) :
    ell ∈ P.interval a ↔ P.left a ≤ ell ∧ ell ≤ P.right a := by
  simp [interval]

theorem prod_Ico_left_distance (l r : ℕ) (hlr : l ≤ r) :
    (∏ s ∈ Finset.Ico l r, ((s : ℤ) - (r : ℤ))) =
      (-1 : ℤ) ^ (r - l) * ((Nat.factorial (r - l) : ℕ) : ℤ) := by
  let d := r - l
  have hshift0 := Finset.prod_Ico_add
    (fun s : ℕ => (s : ℤ) - (r : ℤ)) 0 d l
  have hshift : (∏ s ∈ Finset.Ico l r, ((s : ℤ) - (r : ℤ))) =
      ∏ k ∈ Finset.range d, ((l : ℤ) + (k : ℤ) - (r : ℤ)) := by
    simpa only [d, Nat.Ico_zero_eq_range, Nat.zero_add,
      Nat.sub_add_cancel hlr, Nat.cast_add] using hshift0.symm
  have hterms : (∏ k ∈ Finset.range d, ((l : ℤ) + (k : ℤ) - (r : ℤ))) =
      ∏ k ∈ Finset.range d, -((d - k : ℕ) : ℤ) := by
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hklt := Finset.mem_range.mp hk
    dsimp [d]
    omega
  have hreflect : (∏ k ∈ Finset.range d, ((d - k : ℕ) : ℤ)) =
      ((Nat.factorial d : ℕ) : ℤ) := by
    calc
      _ = ∏ k ∈ Finset.range d, (((d - 1 - k) + 1 : ℕ) : ℤ) := by
        refine Finset.prod_congr (s₁ := Finset.range d) (s₂ := Finset.range d)
          (f := fun k => ((d - k : ℕ) : ℤ))
          (g := fun k => (((d - 1 - k) + 1 : ℕ) : ℤ)) rfl ?_
        intro k hk
        have hklt := Finset.mem_range.mp hk
        congr 1
        omega
      _ = ∏ k ∈ Finset.range d, ((k + 1 : ℕ) : ℤ) :=
        Finset.prod_range_reflect (fun k => ((k + 1 : ℕ) : ℤ)) d
      _ = ((Nat.factorial d : ℕ) : ℤ) := by
        push_cast
        exact_mod_cast Finset.prod_range_add_one_eq_factorial d
  calc
    _ = ∏ k ∈ Finset.range d, -((d - k : ℕ) : ℤ) := hshift.trans hterms
    _ = (-1 : ℤ) ^ (Finset.range d).card *
          ∏ k ∈ Finset.range d, ((d - k : ℕ) : ℤ) := by rw [Finset.prod_neg]
    _ = (-1 : ℤ) ^ d * ((Nat.factorial d : ℕ) : ℤ) := by
      simp [hreflect]
    _ = (-1 : ℤ) ^ (r - l) * ((Nat.factorial (r - l) : ℕ) : ℤ) := by
      simp [d]

theorem prod_Ioc_right_distance (r u : ℕ) (hru : r ≤ u) :
    (∏ s ∈ Finset.Ioc r u, ((s : ℤ) - (r : ℤ))) =
      ((Nat.factorial (u - r) : ℕ) : ℤ) := by
  let d := u - r
  have hshift0 := Finset.prod_Ico_add
    (fun s : ℕ => (s : ℤ) - (r : ℤ)) 1 (d + 1) r
  have hinterval : Finset.Ioc r u = Finset.Ico (r + 1) (u + 1) := by
    ext s
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hd : d + r = u := by dsimp [d]; exact Nat.sub_add_cancel hru
  have hupper : d + 1 + r = u + 1 := by omega
  rw [hinterval]
  calc
    _ = ∏ s ∈ Finset.Ico (1 + r) (d + 1 + r), ((s : ℤ) - (r : ℤ)) := by
      congr 2
      · omega
      · exact hupper.symm
    _ = ∏ k ∈ Finset.Ico 1 (d + 1),
          (((r + k : ℕ) : ℤ) - (r : ℤ)) := hshift0.symm
    _ = ∏ k ∈ Finset.Ico 1 (d + 1), (k : ℤ) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkpos := (Finset.mem_Ico.mp hk).1
      have hklt := (Finset.mem_Ico.mp hk).2
      push_cast
      omega
    _ = ((Nat.factorial d : ℕ) : ℤ) := by
      rw [← Nat.cast_prod]
      exact congrArg (fun n : ℕ => (n : ℤ)) (Finset.prod_Ico_id_eq_factorial d)
    _ = ((Nat.factorial (u - r) : ℕ) : ℤ) := by simp [d]

theorem interval_distance_product (a : Fin M) (ell : ℕ)
    (hmem : ell ∈ P.interval a) :
    (∏ r ∈ Finset.erase (P.interval a) ell, ((r : ℤ) - (ell : ℤ))) =
      (-1 : ℤ) ^ (ell - P.left a) *
        ((Nat.factorial (ell - P.left a) : ℕ) : ℤ) *
        ((Nat.factorial (P.right a - ell) : ℕ) : ℤ) := by
  have hmem' := (P.interval_mem_iff a ell).mp hmem
  have herase : Finset.erase (P.interval a) ell =
      Finset.Ico (P.left a) ell ∪ Finset.Ioc ell (P.right a) := by
    ext r
    constructor
    · intro hr
      obtain ⟨hne, hrmem⟩ := Finset.mem_erase.mp hr
      have hrmem' := (P.interval_mem_iff a r).mp hrmem
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨hrmem'.1, hlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨hgt, hrmem'.2⟩)
    · intro hr
      rcases Finset.mem_union.mp hr with hleft | hright
      · have hleft' := Finset.mem_Ico.mp hleft
        have hrmem : r ∈ P.interval a := by
          apply (P.interval_mem_iff a r).mpr
          exact ⟨hleft'.1, le_trans hleft'.2.le hmem'.2⟩
        exact Finset.mem_erase.mpr ⟨ne_of_lt hleft'.2, hrmem⟩
      · have hright' := Finset.mem_Ioc.mp hright
        have hrmem : r ∈ P.interval a := by
          apply (P.interval_mem_iff a r).mpr
          exact ⟨le_trans hmem'.1 hright'.1.le, hright'.2⟩
        exact Finset.mem_erase.mpr ⟨ne_of_gt hright'.1, hrmem⟩
  have hdisj : Disjoint (Finset.Ico (P.left a) ell) (Finset.Ioc ell (P.right a)) := by
    rw [Finset.disjoint_left]
    intro r hr h'r
    have h1 := Finset.mem_Ico.mp hr
    have h2 := Finset.mem_Ioc.mp h'r
    omega
  rw [herase, Finset.prod_union hdisj]
  rw [prod_Ico_left_distance (P.left a) ell hmem'.1,
    prod_Ioc_right_distance ell (P.right a) hmem'.2]

theorem binomialWeight_mul_distance_product (a : Fin M) (ell : ℕ)
    (hmem : ell ∈ P.interval a) :
    P.binomialWeight a ell *
      (((∏ r ∈ Finset.erase (P.interval a) ell,
        ((r : ℤ) - (ell : ℤ))) : ℤ) : ℚ) =
      (Nat.factorial (P.length a) : ℚ) := by
  have hmem' := (P.interval_mem_iff a ell).mp hmem
  have hlen : P.length a - (ell - P.left a) = P.right a - ell := by
    rw [P.length_eq]
    omega
  have hchoose : Nat.choose (P.length a) (ell - P.left a) *
      (Nat.factorial (ell - P.left a)) * (Nat.factorial (P.right a - ell)) =
      Nat.factorial (P.length a) := by
    have hk : ell - P.left a ≤ P.length a := by
      rw [P.length_eq]
      omega
    simpa [hlen] using Nat.choose_mul_factorial_mul_factorial hk
  have hsign : (-1 : ℚ) ^ (ell - P.left a) *
      (-1 : ℚ) ^ (ell - P.left a) = 1 := by
    rw [← pow_add]
    simp
  rw [binomialWeight, P.interval_distance_product a ell hmem]
  push_cast
  calc
    _ = ((-1 : ℚ) ^ (ell - P.left a) *
          (-1 : ℚ) ^ (ell - P.left a)) *
          ((Nat.choose (P.length a) (ell - P.left a) : ℚ) *
            (Nat.factorial (ell - P.left a) : ℚ) *
            (Nat.factorial (P.right a - ell) : ℚ)) := by ring
    _ = (Nat.choose (P.length a) (ell - P.left a) : ℚ) *
          (Nat.factorial (ell - P.left a) : ℚ) *
          (Nat.factorial (P.right a - ell) : ℚ) := by rw [hsign, one_mul]
    _ = (Nat.factorial (P.length a) : ℚ) := by exact_mod_cast hchoose

theorem interval_antitone {a b : Fin M} (hab : a ≤ b) :
    P.interval b ⊆ P.interval a := by
  intro ell hell
  rw [P.interval_mem_iff] at hell ⊢
  have hleft := P.left_mono hab
  have hright : P.right b ≤ P.right a := by
    exact Nat.sub_le_sub_left hleft P.n
  exact ⟨le_trans hleft hell.1, hell.2.trans hright⟩

theorem multiplicity_support_iff (j : Fin M) (ell : ℕ) :
    j.val + 1 ≤ P.multiplicity ell ↔ ell ∈ P.interval j := by
  classical
  constructor
  · intro hmu
    by_contra hnot
    have hsubset : P.poleIndices ell ⊆ Finset.Iio j := by
      intro a ha
      have ha' : ell ∈ P.interval a := by
        simpa [poleIndices] using ha
      have hlt : a < j := by
        by_contra h
        have hja : j ≤ a := le_of_not_gt h
        have hmem := P.interval_antitone hja ha'
        exact hnot hmem
      exact Finset.mem_Iio.mpr hlt
    have hcard := Finset.card_le_card hsubset
    have hmu' : P.multiplicity ell ≤ j.val := by
      simpa [multiplicity, poleIndices] using hcard
    omega
  · intro hj
    have hsubset : Finset.Iic j ⊆ P.poleIndices ell := by
      intro a ha
      have haj : a ≤ j := Finset.mem_Iic.mp ha
      have hmem := P.interval_antitone haj hj
      simp [poleIndices, hmem]
    have hcard := Finset.card_le_card hsubset
    have hmu' : j.val + 1 ≤ P.multiplicity ell := by
      simpa [multiplicity, poleIndices] using hcard
    exact hmu'

noncomputable def poleLocalFactor (a : Fin M) (ell : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (P.binomialWeight a ell) *
    ∏ r ∈ Finset.erase (P.interval a) ell,
      normalizedReciprocal ((r : ℤ) - (ell : ℤ))

noncomputable def regularLocalFactor (a : Fin M) (ell : ℕ) : PowerSeries ℚ :=
  ∑ r ∈ P.interval a,
    PowerSeries.C (P.binomialWeight a r) *
      regularReciprocal ((r : ℤ) - (ell : ℤ))

/-- The numerator obtained by clearing the denominator in the finite interval
partial fraction formula at the local coordinate `z = -ell + X`. -/
noncomputable def clearedPartialFractionPolynomial (a : Fin M) (ell : ℕ) : Polynomial ℚ :=
  ∑ r ∈ P.interval a,
    C (P.binomialWeight a r) *
      ∏ s ∈ (P.interval a).erase r,
        (X + C ((s : ℚ) - (ell : ℚ)))

theorem clearedPartialFractionPolynomial_natDegree_le (a : Fin M) (ell : ℕ) :
    (P.clearedPartialFractionPolynomial a ell).natDegree ≤ P.length a := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  have hcard : ((P.interval a).erase r).card = P.length a := by
    rw [Finset.card_erase_of_mem hr]
    simp [interval, length, right]
    omega
  have hprod : (∏ s ∈ (P.interval a).erase r,
      (X + C ((s : ℚ) - (ell : ℚ)))).natDegree ≤ P.length a := by
    calc
      _ ≤ ∑ s ∈ (P.interval a).erase r,
            (X + C ((s : ℚ) - (ell : ℚ))).natDegree :=
          Polynomial.natDegree_prod_le ((P.interval a).erase r)
            (fun s => X + C ((s : ℚ) - (ell : ℚ)))
      _ ≤ ∑ s ∈ (P.interval a).erase r, 1 := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Polynomial.natDegree_X_add_C]
      _ = P.length a := by simp [hcard]
  exact (Polynomial.natDegree_C_mul_le _ _).trans hprod

/-- Clearing the denominator in the finite partial fraction sum gives the
interval factorial.  The evaluation points are distinct because they are
the negatives of the interval indices. -/
theorem clearedPartialFractionPolynomial_eq_factorial (a : Fin M) (ell : ℕ) :
    P.clearedPartialFractionPolynomial a ell =
      C (Nat.factorial (P.length a) : ℚ) := by
  classical
  let S := P.interval a
  let f : {r // r ∈ S} → ℚ := fun r => (ell : ℚ) - (r.val : ℚ)
  have hf : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    have hcast : (r.val : ℚ) = (s.val : ℚ) := by
      exact sub_right_injective hrs
    exact_mod_cast hcast
  have hcard : Fintype.card {r // r ∈ S} = P.length a + 1 := by
    rw [Fintype.card_coe]
    simp [S, interval, length, right]
    have hbound := P.left_bound a
    omega
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
      (f := f)
  · exact hf
  · intro r
    have hrmem : r.val ∈ P.interval a := r.property
    have hmain :
        Polynomial.eval (f r)
          (C (P.binomialWeight a r.val) *
            ∏ s ∈ (P.interval a).erase r.val,
              (X + C ((s : ℚ) - (ell : ℚ)))) =
          (Nat.factorial (P.length a) : ℚ) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      calc
        _ = P.binomialWeight a r.val *
              ∏ s ∈ (P.interval a).erase r.val, ((s : ℚ) - (r.val : ℚ)) := by
            congr 1
            apply Finset.prod_congr rfl
            intro s hs
            dsimp [f]
            ring
        _ = (Nat.factorial (P.length a) : ℚ) := by
            have hdist :
                (∏ s ∈ (P.interval a).erase r.val,
                    ((s : ℚ) - (r.val : ℚ))) =
                  ((((∏ s ∈ (P.interval a).erase r.val,
                    ((s : ℤ) - (r.val : ℤ))) : ℤ) : ℚ)) := by
              norm_cast
            rw [hdist]
            exact P.binomialWeight_mul_distance_product a r.val hrmem
    rw [clearedPartialFractionPolynomial, Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single_of_mem r.val hrmem]
    · simpa only [Polynomial.eval_C] using hmain
    · intro q hq hqr
      have hzero :
          Polynomial.eval (f r)
            (∏ s ∈ (P.interval a).erase q,
              (X + C ((s : ℚ) - (ell : ℚ)))) = 0 := by
        rw [Polynomial.eval_prod]
        apply Finset.prod_eq_zero
        · exact Finset.mem_erase.mpr ⟨Ne.symm hqr, hrmem⟩
        · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
          dsimp [f]
          ring
      rw [Polynomial.eval_mul, Polynomial.eval_C, hzero, mul_zero]
  · rw [hcard]
    have hdeg := P.clearedPartialFractionPolynomial_natDegree_le a ell
    rw [Polynomial.natDegree_C]
    omega

/-- The signed binomial partial fractions are the actual reciprocal of the
local interval denominator when the expansion point is regular. -/
theorem regularLocalFactor_mul_localDenominator (a : Fin M) (ell : ℕ)
    (hmem : ell ∉ P.interval a) :
    P.regularLocalFactor a ell *
        ∏ r ∈ P.interval a,
          (PowerSeries.C ((r : ℚ) - (ell : ℚ)) + PowerSeries.X) =
      PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by
  classical
  let L : ℕ → PowerSeries ℚ :=
    fun r => PowerSeries.C ((r : ℚ) - (ell : ℚ)) + PowerSeries.X
  have hpoly := congrArg (fun p : Polynomial ℚ => (p : PowerSeries ℚ))
    (P.clearedPartialFractionPolynomial_eq_factorial a ell)
  have hbridge :
      (∑ r ∈ P.interval a,
        PowerSeries.C (P.binomialWeight a r) *
          ∏ s ∈ (P.interval a).erase r, L s) =
        (P.clearedPartialFractionPolynomial a ell : PowerSeries ℚ) := by
    change (∑ r ∈ P.interval a,
        PowerSeries.C (P.binomialWeight a r) *
          ∏ s ∈ (P.interval a).erase r, L s) =
        Polynomial.coeToPowerSeries.ringHom
          (∑ r ∈ P.interval a,
            C (P.binomialWeight a r) *
              ∏ s ∈ (P.interval a).erase r,
                (X + C ((s : ℚ) - (ell : ℚ))))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [map_mul]
    congr 1
    · simp
    · rw [map_prod]
      apply Finset.prod_congr rfl
      intro s hs
      rw [map_add]
      simp only [Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_X, Polynomial.coe_C]
      dsimp [L]
      exact add_comm (PowerSeries.C ((s : ℚ) - (ell : ℚ))) PowerSeries.X
  calc
    _ = ∑ r ∈ P.interval a,
          (PowerSeries.C (P.binomialWeight a r) *
            regularReciprocal ((r : ℤ) - (ell : ℤ))) *
              ∏ s ∈ P.interval a, L s := by
          simp [regularLocalFactor, L, Finset.sum_mul]
    _ = ∑ r ∈ P.interval a,
          PowerSeries.C (P.binomialWeight a r) *
            ∏ s ∈ (P.interval a).erase r, L s := by
          apply Finset.sum_congr rfl
          intro r hr
          let e : ℤ := (r : ℤ) - (ell : ℤ)
          have he : e ≠ 0 := by
            intro he0
            apply hmem
            have hcast : (r : ℤ) = (ell : ℤ) := sub_eq_zero.mp (by simpa [e] using he0)
            have hrEq : r = ell := Int.ofNat.inj hcast
            simpa [hrEq] using hr
          have hL : L r = PowerSeries.C (e : ℚ) + PowerSeries.X := by
            simp [L, e]
          have hsplit := Finset.mul_prod_erase (P.interval a) L hr
          rw [← hsplit, hL]
          calc
            _ = PowerSeries.C (P.binomialWeight a r) *
                  ((PowerSeries.C (e : ℚ) + PowerSeries.X) *
                    regularReciprocal e * ∏ s ∈ (P.interval a).erase r, L s) := by
                  ring
            _ = PowerSeries.C (P.binomialWeight a r) *
                  ∏ s ∈ (P.interval a).erase r, L s := by
                  rw [regularReciprocal_identity e he]
                  simp
    _ = PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by
          rw [hbridge]
          rw [Polynomial.coe_C] at hpoly
          exact hpoly

/-- In the pole case, multiplying the regularized local factor by the
nonvanishing denominator factors also gives the interval factorial. -/
theorem poleLocalFactor_mul_localDenominator (a : Fin M) (ell : ℕ)
    (hmem : ell ∈ P.interval a) :
    P.poleLocalFactor a ell *
        ∏ r ∈ (P.interval a).erase ell,
          (PowerSeries.C ((r : ℚ) - (ell : ℚ)) + PowerSeries.X) =
      PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by
  classical
  let S := (P.interval a).erase ell
  let e : ℕ → ℤ := fun r => (r : ℤ) - (ell : ℤ)
  let L : ℕ → PowerSeries ℚ :=
    fun r => PowerSeries.C ((r : ℚ) - (ell : ℚ)) + PowerSeries.X
  have hfactor : ∀ r ∈ S,
      normalizedReciprocal (e r) * L r = PowerSeries.C (e r : ℚ) := by
    intro r hr
    have hne : e r ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      exact (Finset.mem_erase.mp hr).1 (Int.ofNat.inj h)
    have hneQ : (e r : ℚ) ≠ 0 := by exact_mod_cast hne
    have hscalar : (e r : ℚ) * (1 / (e r : ℚ)) = 1 := by
      field_simp [hneQ]
    have hC : PowerSeries.C (e r : ℚ) * PowerSeries.C (1 / (e r : ℚ)) = 1 := by
      have hc := congrArg (PowerSeries.C : ℚ → PowerSeries ℚ) hscalar
      simpa using hc
    have hL : L r = PowerSeries.C (e r : ℚ) + PowerSeries.X := by
      simp [L, e]
    have hsplit : PowerSeries.C (e r : ℚ) + PowerSeries.X =
        PowerSeries.C (e r : ℚ) *
          (1 + PowerSeries.C (1 / (e r : ℚ)) * PowerSeries.X) := by
      calc
        _ = PowerSeries.C (e r : ℚ) +
              (PowerSeries.C (e r : ℚ) * PowerSeries.C (1 / (e r : ℚ))) *
                PowerSeries.X := by rw [hC]; simp
        _ = _ := by ring
    rw [hL, hsplit]
    calc
      _ = PowerSeries.C (e r : ℚ) *
            ((1 + PowerSeries.C (1 / (e r : ℚ)) * PowerSeries.X) *
              normalizedReciprocal (e r)) := by ring
      _ = PowerSeries.C (e r : ℚ) := by
            rw [normalizedReciprocal_identity]
            simp
  have hprod :
      (∏ r ∈ S, normalizedReciprocal (e r)) * (∏ r ∈ S, L r) =
        ∏ r ∈ S, PowerSeries.C (e r : ℚ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r hr
    exact hfactor r hr
  have hdist :
      (∏ r ∈ S, (e r : ℚ)) = ((((∏ r ∈ S, e r) : ℤ) : ℚ)) := by
    norm_cast
  have hCprod :
      (∏ r ∈ S, PowerSeries.C (e r : ℚ)) =
        PowerSeries.C (∏ r ∈ S, (e r : ℚ)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert r S hr ih =>
      rw [Finset.prod_insert hr, Finset.prod_insert hr, ih, ← map_mul]
  calc
    _ = PowerSeries.C (P.binomialWeight a ell) *
          ((∏ r ∈ S, normalizedReciprocal (e r)) * (∏ r ∈ S, L r)) := by
          simp [poleLocalFactor, S, L, e]
          ring
    _ = PowerSeries.C (P.binomialWeight a ell) *
          ∏ r ∈ S, PowerSeries.C (e r : ℚ) := by rw [hprod]
    _ = PowerSeries.C
          (P.binomialWeight a ell * ∏ r ∈ S, (e r : ℚ)) := by
          rw [hCprod]
          simp
    _ = PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by
          rw [hdist]
          exact congrArg PowerSeries.C
            (P.binomialWeight_mul_distance_product a ell hmem)

/-- Local expansion of a normalized interval factor at `z = -ell`.  The pole
case uses the binomial constant and normalized reciprocals; the regular case
is the integer-weighted partial fraction sum. -/
noncomputable def localFactor (a : Fin M) (ell : ℕ) : PowerSeries ℚ := by
  classical
  exact if ell ∈ P.interval a then
    P.poleLocalFactor a ell
  else
    P.regularLocalFactor a ell

/-- The full regularized local expansion of `z^h * ∏ₐ length(a)!/denominatorₐ`.
Its coefficient of order `multiplicity(ell)-j-1` is the relevant partial
fraction coefficient for column `j`. -/
noncomputable def localExpansion (ell h : ℕ) : PowerSeries ℚ :=
  (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X) ^ h *
    ∏ a : Fin M, P.localFactor a ell

/-- The common unit factor after removing the pole order at `-ell`. -/
noncomputable def localUnit (ell : ℕ) : PowerSeries ℚ :=
  ∏ a : Fin M, P.localFactor a ell

/-- The product of the nonvanishing linear factors contributed by one
interval after translating the expansion point to `z = -ell + X`. -/
noncomputable def intervalLocalDenominator (a : Fin M) (ell : ℕ) :
    PowerSeries ℚ :=
  ∏ r ∈ (Finset.range (P.n + 1)).filter
      (fun r => r ∈ P.interval a ∧ r ≠ ell),
    (PowerSeries.C ((r : ℚ) - (ell : ℚ)) + PowerSeries.X)

/-- The product of all nonvanishing root factors at the translated local
coordinate. -/
noncomputable def localRootDenominator (ell : ℕ) : PowerSeries ℚ :=
  ∏ r ∈ Finset.range (P.n + 1),
    if r = ell then 1 else
      (PowerSeries.C ((r : ℚ) - (ell : ℚ)) + PowerSeries.X) ^
        P.multiplicity r

/-- A translated root product with the pole and expansion point allowed to
vary independently. -/
noncomputable def translatedOtherRootDenominator (pole center : ℕ) :
    PowerSeries ℚ :=
  ∏ r ∈ Finset.range (P.n + 1),
    if r = pole then 1 else
      (PowerSeries.C ((r : ℚ) - (center : ℚ)) + PowerSeries.X) ^
        P.multiplicity r

/-- The polynomial denominator with the root at `-ell` removed. -/
noncomputable def otherRootProduct (ell : ℕ) : Polynomial ℚ :=
  ∏ r ∈ Finset.range (P.n + 1),
    if r = ell then 1 else
      (X + C (r : ℚ)) ^ P.multiplicity r

/-- One cleared principal-part summand at a specified repeated pole. -/
noncomputable def partialFractionTerm (h pole q : ℕ) : Polynomial ℚ :=
  C (PowerSeries.coeff q (P.localExpansion pole h)) *
    (X + C (pole : ℚ)) ^ q * P.otherRootProduct pole

/-- The finite Taylor truncation containing exactly the principal-part
coefficients at a given pole. -/
noncomputable def principalPartTruncation (ell h : ℕ) : PowerSeries ℚ :=
  ∑ q ∈ Finset.range (P.multiplicity ell),
    PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h)) *
      PowerSeries.X ^ q

/-- The cleared numerator formed from the principal-part coefficients at all
actual repeated poles. The coefficient of local order `q` multiplies the
`q`th power of the pole factor. -/
noncomputable def partialFractionNumerator (h : ℕ) : Polynomial ℚ :=
  ∑ ell ∈ Finset.range (P.n + 1),
    ∑ q ∈ Finset.range (P.multiplicity ell),
      P.partialFractionTerm h ell q

/-- The coefficient of the pole term corresponding to column `j`; it is zero
when the pole order is too small for that column. -/
noncomputable def localCoefficient (ell h j : ℕ) : ℚ :=
  if j < P.multiplicity ell then
    PowerSeries.coeff (P.multiplicity ell - 1 - j) (P.localExpansion ell h)
  else 0

theorem binomialWeight_mem (a : Fin M) (r : ℕ) :
    P.binomialWeight a r ∈ integerRationals := by
  change (((-1 : ℤ) ^ (r - P.left a) *
    (Nat.choose (P.length a) (r - P.left a) : ℤ)) : ℚ) ∈ integerRationals
  apply integerRationals.mul_mem
  · have h := intCast_mem_integerRationals ((-1 : ℤ) ^ (r - P.left a))
    simpa using h
  · have h := intCast_mem_integerRationals (Nat.choose (P.length a) (r - P.left a) : ℤ)
    exact_mod_cast h

theorem localDistance_ne_and_bound (a : Fin M) (ell : ℕ) (hell : ell ≤ P.n)
    {r : ℕ} (hr : r ∈ P.interval a) (hne : r ≠ ell) :
    ((r : ℤ) - (ell : ℤ)) ≠ 0 ∧
      Int.natAbs ((r : ℤ) - (ell : ℤ)) ≤ P.n := by
  have hr' := (P.interval_mem_iff a r).mp hr
  have hrn : r ≤ P.n := le_trans hr'.2 (P.right_le_n a)
  have hlow : -(P.n : ℤ) ≤ (r : ℤ) - (ell : ℤ) := by omega
  have hhigh : (r : ℤ) - (ell : ℤ) ≤ P.n := by omega
  have habsInt : ((((r : ℤ) - (ell : ℤ)).natAbs : ℕ) : ℤ) ≤ P.n := by
    by_cases hnonneg : 0 ≤ (r : ℤ) - (ell : ℤ)
    · rw [Int.natAbs_of_nonneg hnonneg]
      exact hhigh
    · have hnonpos : (r : ℤ) - (ell : ℤ) ≤ 0 := le_of_not_ge hnonneg
      have hcast : ((((r : ℤ) - (ell : ℤ)).natAbs : ℕ) : ℤ) =
          -((r : ℤ) - (ell : ℤ)) := Int.ofNat_natAbs_of_nonpos hnonpos
      calc
        ((((r : ℤ) - (ell : ℤ)).natAbs : ℕ) : ℤ) =
            -((r : ℤ) - (ell : ℤ)) := hcast
        _ ≤ P.n := by omega
  have habs : Int.natAbs ((r : ℤ) - (ell : ℤ)) ≤ P.n := by
    exact_mod_cast habsInt
  constructor
  · intro h
    have hcast : (r : ℤ) = (ell : ℤ) := sub_eq_zero.mp h
    exact hne (Int.ofNat.inj hcast)
  · simpa using habs

theorem poleLocalFactor_cleared (a : Fin M) (ell : ℕ) (hell : ell ≤ P.n) :
    DenominatorCleared (intervalLcm P.n) 0 (P.poleLocalFactor a ell) := by
  classical
  let w : ℤ := (-1 : ℤ) ^ (ell - P.left a) *
    (Nat.choose (P.length a) (ell - P.left a) : ℤ)
  have hweight : P.binomialWeight a ell = (w : ℚ) := by
    simp [binomialWeight, w]
  have hgood : ∀ r ∈ Finset.erase (P.interval a) ell,
      ((r : ℤ) - (ell : ℤ)) ≠ 0 ∧
        ((r : ℤ) - (ell : ℤ)) ∣ (intervalLcm P.n : ℤ) := by
    intro r hr
    have hrmem : r ∈ P.interval a := (Finset.mem_erase.mp hr).2
    have hrne : r ≠ ell := (Finset.mem_erase.mp hr).1
    obtain ⟨hne, hlen⟩ := P.localDistance_ne_and_bound a ell hell hrmem hrne
    exact ⟨hne, boundedDistance_dvd_intervalLcm P.n _ hne hlen⟩
  have hp := poleLocalProduct_cleared (Finset.erase (P.interval a) ell)
    (intervalLcm P.n : ℤ) w (fun r => (r : ℤ) - (ell : ℤ))
    (fun r hr => (hgood r hr).1) (fun r hr => (hgood r hr).2)
  simpa [poleLocalFactor, binomialWeight, w] using hp

theorem regularLocalFactor_cleared (a : Fin M) (ell : ℕ) (hell : ell ≤ P.n)
    (hmem : ell ∉ P.interval a) :
    DenominatorCleared (intervalLcm P.n) 1 (P.regularLocalFactor a ell) := by
  classical
  let w : ℕ → ℤ := fun r =>
    (-1 : ℤ) ^ (r - P.left a) * (Nat.choose (P.length a) (r - P.left a) : ℤ)
  let e : ℕ → ℤ := fun r => (r : ℤ) - (ell : ℤ)
  have hgood : ∀ r ∈ P.interval a, e r ≠ 0 ∧ e r ∣ (intervalLcm P.n : ℤ) := by
    intro r hr
    have hrne : r ≠ ell := by
      intro heq
      apply hmem
      rw [← heq]
      exact hr
    obtain ⟨hne, hlen⟩ := P.localDistance_ne_and_bound a ell hell hr hrne
    exact ⟨by simpa [e] using hne,
      boundedDistance_dvd_intervalLcm P.n (e r) (by simpa [e] using hne)
        (by simpa [e] using hlen)⟩
  have hp := regularLocalSum_cleared (P.interval a) (intervalLcm P.n : ℤ)
    w e (fun r hr => (hgood r hr).1) (fun r hr => (hgood r hr).2)
  simpa [regularLocalFactor, binomialWeight, w, e] using hp

theorem poleLocalFactor_constantCoeff_ne_zero (a : Fin M) (ell : ℕ)
    (hmem : ell ∈ P.interval a) :
    PowerSeries.constantCoeff (P.poleLocalFactor a ell) ≠ 0 := by
  have hfac : (Nat.factorial (P.length a) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (P.length a)
  have hweight : P.binomialWeight a ell ≠ 0 := by
    intro hz
    have h := P.binomialWeight_mul_distance_product a ell hmem
    rw [hz, zero_mul] at h
    exact hfac h.symm
  have hcc : PowerSeries.constantCoeff (P.poleLocalFactor a ell) =
      P.binomialWeight a ell := by
    simp [poleLocalFactor, normalizedReciprocal]
  rw [hcc]
  exact hweight

theorem regularLocalFactor_constantCoeff_ne_zero (a : Fin M) (ell : ℕ)
    (hmem : ell ∉ P.interval a) :
    PowerSeries.constantCoeff (P.regularLocalFactor a ell) ≠ 0 := by
  have hfac : (Nat.factorial (P.length a) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (P.length a)
  have h := congrArg PowerSeries.constantCoeff
    (P.regularLocalFactor_mul_localDenominator a ell hmem)
  intro hz
  have hzero : (0 : ℚ) = (Nat.factorial (P.length a) : ℚ) := by
    simpa [hz] using h
  exact hfac hzero.symm

theorem localFactor_constantCoeff_ne_zero (a : Fin M) (ell : ℕ) :
    PowerSeries.constantCoeff (P.localFactor a ell) ≠ 0 := by
  classical
  by_cases hmem : ell ∈ P.interval a
  · simpa [localFactor, hmem] using P.poleLocalFactor_constantCoeff_ne_zero a ell hmem
  · simpa [localFactor, hmem] using P.regularLocalFactor_constantCoeff_ne_zero a ell hmem

theorem localUnit_constantCoeff_ne_zero (ell : ℕ) :
    PowerSeries.constantCoeff (P.localUnit ell) ≠ 0 := by
  classical
  simp only [localUnit, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact P.localFactor_constantCoeff_ne_zero a ell

theorem localFactor_cleared (a : Fin M) (ell : ℕ) (hell : ell ≤ P.n) :
    DenominatorCleared (intervalLcm P.n)
      (if ell ∈ P.interval a then 0 else 1) (P.localFactor a ell) := by
  classical
  by_cases hmem : ell ∈ P.interval a
  · simpa [localFactor, hmem] using P.poleLocalFactor_cleared a ell hell
  · simpa [localFactor, hmem] using P.regularLocalFactor_cleared a ell hell hmem

theorem localExpansion_cleared (ell h : ℕ) (hell : ell ≤ P.n) :
    DenominatorCleared (intervalLcm P.n) (M - P.multiplicity ell)
      (P.localExpansion ell h) := by
  classical
  let d : ℤ := intervalLcm P.n
  let b : Fin M → ℕ := fun a => if ell ∈ P.interval a then 0 else 1
  have hprod := denominatorCleared_prod Finset.univ d b
    (fun a => P.localFactor a ell) (by
      intro a _
      simpa [d, b] using P.localFactor_cleared a ell hell)
  have hsum : (∑ a : Fin M, b a) = M - P.multiplicity ell := by
    have hcnt : (Finset.univ.filter (fun a : Fin M => ell ∉ P.interval a)).card =
        M - P.multiplicity ell := by
      have hparts := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (p := fun a : Fin M => ell ∈ P.interval a)
      have hparts' : P.multiplicity ell +
          (Finset.univ.filter (fun a : Fin M => ell ∉ P.interval a)).card = M := by
        simpa [multiplicity, add_comm] using hparts
      omega
    calc
      _ = (Finset.univ.filter (fun a : Fin M => ell ∉ P.interval a)).card := by
        have hrewrite : (∑ a : Fin M, b a) =
            ∑ a : Fin M, if ell ∉ P.interval a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : ell ∈ P.interval a <;> simp [b, ha]
        rw [hrewrite]
        have hcardSum : (Finset.univ.filter
            (fun a : Fin M => ell ∉ P.interval a)).card =
            ∑ a : Fin M, if ell ∉ P.interval a then 1 else 0 := by
          simpa using (Finset.card_eq_sum_ite
            (s := Finset.univ.filter (fun a : Fin M => ell ∉ P.interval a))
            (t := Finset.univ) (by simp))
        exact hcardSum.symm
      _ = M - P.multiplicity ell := hcnt
  have hprod' : DenominatorCleared (intervalLcm P.n)
      (M - P.multiplicity ell) (∏ a : Fin M, P.localFactor a ell) := by
    simpa only [d, ← hsum] using hprod
  have hnum := polynomialNumerator_cleared (intervalLcm P.n) (ell : ℤ) h
  simpa [localExpansion] using hnum.mul hprod'

/-- Regroup the interval denominator by its distinct integer roots. -/
theorem denominator_eq_rootProduct :
    P.denominator =
      ∏ ell ∈ Finset.range (P.n + 1),
        (X + C (ell : ℚ)) ^ P.multiplicity ell := by
  classical
  have hinterval (a : Fin M) : P.interval a =
      (Finset.range (P.n + 1)).filter (fun ell => ell ∈ P.interval a) := by
    ext ell
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      have hle := (P.interval_mem_iff a ell).mp h
      have hrn := P.right_le_n a
      exact ⟨by omega, h⟩
    · exact fun h => h.2
  unfold denominator
  calc
    _ = ∏ a : Fin M, ∏ ell ∈ Finset.range (P.n + 1),
          if ell ∈ P.interval a then X + C (ell : ℚ) else 1 := by
          apply Finset.prod_congr rfl
          intro a ha
          rw [hinterval a, Finset.prod_filter]
          apply Finset.prod_congr rfl
          intro ell hell
          simp [Finset.mem_filter, hell]
    _ = ∏ ell ∈ Finset.range (P.n + 1),
          ∏ a : Fin M,
            if ell ∈ P.interval a then X + C (ell : ℚ) else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ ell ∈ Finset.range (P.n + 1),
          (X + C (ell : ℚ)) ^ P.multiplicity ell := by
          apply Finset.prod_congr rfl
          intro ell hell
          rw [← Finset.prod_filter]
          simp [multiplicity, Finset.prod_const]

theorem totalMultiplicity_eq_sum_interval_card :
    P.totalMultiplicity = ∑ a : Fin M, (P.interval a).card := by
  classical
  unfold totalMultiplicity
  calc
    _ = ∑ ell ∈ Finset.range (P.n + 1),
          ∑ a : Fin M, if ell ∈ P.interval a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro ell hell
          rw [multiplicity]
          have hcard := Finset.card_eq_sum_ite
            (s := Finset.univ.filter (fun a : Fin M => ell ∈ P.interval a))
            (t := Finset.univ) (by intro a ha; simp)
          simpa [Finset.mem_filter] using hcard
    _ = ∑ a : Fin M, ∑ ell ∈ Finset.range (P.n + 1),
          if ell ∈ P.interval a then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a : Fin M, (P.interval a).card := by
          apply Finset.sum_congr rfl
          intro a ha
          symm
          apply Finset.card_eq_sum_ite
          intro ell hell
          have hmem := (P.interval_mem_iff a ell).mp hell
          have hright := P.right_le_n a
          simp only [Finset.mem_range]
          omega

theorem interval_card_eq_length_add_one (a : Fin M) :
    (P.interval a).card = P.length a + 1 := by
  rw [interval, Nat.card_Icc, P.length_eq]
  have h := P.left_le_right a
  omega

theorem totalMultiplicity_eq_card_add_sum_length :
    P.totalMultiplicity = M + ∑ a : Fin M, P.length a := by
  rw [P.totalMultiplicity_eq_sum_interval_card]
  simp_rw [P.interval_card_eq_length_add_one]
  rw [Finset.sum_add_distrib]
  simp [Nat.add_comm]

theorem totalMultiplicity_ge_card : M ≤ P.totalMultiplicity := by
  classical
  rw [P.totalMultiplicity_eq_sum_interval_card]
  have hsum : (∑ a : Fin M, (1 : ℕ)) ≤
      ∑ a : Fin M, (P.interval a).card :=
    Finset.sum_le_sum fun a ha => by
      have hleft : P.left a ∈ P.interval a := by
        apply (P.interval_mem_iff a (P.left a)).mpr
        exact ⟨le_rfl, P.left_le_right a⟩
      have hpos := Finset.card_pos.mpr ⟨P.left a, hleft⟩
      omega
  simpa using hsum

/-- The local denominator contributed by one interval is exactly the
product over its roots other than the expansion point. -/
theorem localFactor_mul_intervalLocalDenominator (a : Fin M) (ell : ℕ) :
    P.localFactor a ell * P.intervalLocalDenominator a ell =
      PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by
  classical
  by_cases hmem : ell ∈ P.interval a
  · have hset :
        (Finset.range (P.n + 1)).filter
            (fun r => r ∈ P.interval a ∧ r ≠ ell) =
          (P.interval a).erase ell := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨_, hrmem, hrne⟩
        exact ⟨hrne, hrmem⟩
      · rintro ⟨hrne, hrmem⟩
        have hrle := (P.interval_mem_iff a r).mp hrmem |>.2
        have hright := P.right_le_n a
        exact ⟨by omega, hrmem, hrne⟩
    rw [localFactor, if_pos hmem, intervalLocalDenominator, hset]
    exact P.poleLocalFactor_mul_localDenominator a ell hmem
  · have hset :
        (Finset.range (P.n + 1)).filter
            (fun r => r ∈ P.interval a ∧ r ≠ ell) = P.interval a := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, hrmem, _⟩
        exact hrmem
      · intro hrmem
        have hrle := (P.interval_mem_iff a r).mp hrmem |>.2
        have hright := P.right_le_n a
        refine ⟨by omega, hrmem, ?_⟩
        intro heq
        exact hmem (heq ▸ hrmem)
    rw [localFactor, if_neg hmem, intervalLocalDenominator, hset]
    exact P.regularLocalFactor_mul_localDenominator a ell hmem

/-- Regrouping the interval local denominators gives the global translated
denominator with each root repeated according to its actual multiplicity. -/
theorem prod_intervalLocalDenominator_eq_localRootDenominator (ell : ℕ) :
    (∏ a : Fin M, P.intervalLocalDenominator a ell) =
      P.localRootDenominator ell := by
  classical
  let L : ℕ → PowerSeries ℚ := fun r =>
    PowerSeries.C ((r : ℚ) - (ell : ℚ)) + PowerSeries.X
  have hrewrite (a : Fin M) :
      P.intervalLocalDenominator a ell =
        ∏ r ∈ Finset.range (P.n + 1),
          if r ∈ P.interval a ∧ r ≠ ell then L r else 1 := by
    rw [intervalLocalDenominator, Finset.prod_filter]
  have hinner (r : ℕ) :
      (∏ a : Fin M,
          if r ∈ P.interval a ∧ r ≠ ell then L r else 1) =
        (if r = ell then 1 else L r ^ P.multiplicity r) := by
    by_cases hr : r = ell
    · subst r
      simp
    · have hprod :
          (∏ a : Fin M,
              if r ∈ P.interval a ∧ r ≠ ell then L r else 1) =
            ∏ a : Fin M, if r ∈ P.interval a then L r else 1 := by
          apply Finset.prod_congr rfl
          intro a ha
          simp [hr]
      rw [hprod, ← Finset.prod_filter]
      simp [hr, multiplicity, Finset.prod_const, L]
  calc
    _ = ∏ a : Fin M, ∏ r ∈ Finset.range (P.n + 1),
          if r ∈ P.interval a ∧ r ≠ ell then L r else 1 := by
          apply Finset.prod_congr rfl
          intro a ha
          exact hrewrite a
    _ = ∏ r ∈ Finset.range (P.n + 1),
          ∏ a : Fin M,
            if r ∈ P.interval a ∧ r ≠ ell then L r else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ r ∈ Finset.range (P.n + 1),
          (if r = ell then 1 else L r ^ P.multiplicity r) := by
          apply Finset.prod_congr rfl
          intro r hr
          exact hinner r
    _ = P.localRootDenominator ell := by
          simp [localRootDenominator, L]

/-- The product of the local regularized factors and their complementary
denominators is the product of the interval factorials. -/
theorem localUnit_mul_localRootDenominator (ell : ℕ) :
    P.localUnit ell * P.localRootDenominator ell =
      PowerSeries.C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) := by
  classical
  have hintervals :
      (∏ a : Fin M, P.localFactor a ell) *
          (∏ a : Fin M, P.intervalLocalDenominator a ell) =
        ∏ a : Fin M, PowerSeries.C (Nat.factorial (P.length a) : ℚ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a ha
    exact P.localFactor_mul_intervalLocalDenominator a ell
  have hCprod :
      (∏ a : Fin M, PowerSeries.C (Nat.factorial (P.length a) : ℚ)) =
        PowerSeries.C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) := by
    induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, ← map_mul]
  calc
    _ = (∏ a : Fin M, P.localFactor a ell) *
          (∏ a : Fin M, P.intervalLocalDenominator a ell) := by
            rw [localUnit, P.prod_intervalLocalDenominator_eq_localRootDenominator]
    _ = ∏ a : Fin M, PowerSeries.C (Nat.factorial (P.length a) : ℚ) := hintervals
    _ = PowerSeries.C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) := hCprod

/-- The translated original numerator, after clearing the local unit
denominator, is exactly the product of interval factorials. -/
theorem localExpansion_mul_localRootDenominator (ell h : ℕ) :
    P.localExpansion ell h * P.localRootDenominator ell =
      PowerSeries.C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
        (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X) ^ h := by
  calc
    _ = (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X) ^ h *
          (P.localUnit ell * P.localRootDenominator ell) := by
            simp [localExpansion, localUnit, mul_assoc]
    _ = _ := by rw [P.localUnit_mul_localRootDenominator]; ring

/-- Translating the polynomial with the `ell` root removed gives the
corresponding regular local denominator power series. -/
theorem otherRootProduct_taylorAt (pole center : ℕ) :
    Polynomial.coeToPowerSeries.ringHom
        ((P.otherRootProduct pole).taylor (-(center : ℚ))) =
      P.translatedOtherRootDenominator pole center := by
  classical
  have hpoly :
      (P.otherRootProduct pole).taylor (-(center : ℚ)) =
        ∏ r ∈ Finset.range (P.n + 1),
          if r = pole then 1 else
            (X + C ((r : ℚ) - (center : ℚ))) ^ P.multiplicity r := by
    change Polynomial.taylorAlgHom (-(center : ℚ))
      (∏ r ∈ Finset.range (P.n + 1),
        if r = pole then 1 else (X + C (r : ℚ)) ^ P.multiplicity r) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro r hr
    by_cases heq : r = pole
    · simp [heq]
    · have hbase :
          Polynomial.taylorAlgHom (-(center : ℚ)) (X + C (r : ℚ)) =
            X + C ((r : ℚ) - (center : ℚ)) := by
          change (X + C (r : ℚ)).taylor (-(center : ℚ)) = _
          simp [Polynomial.taylor_apply]
          ring
      simp only [if_neg heq, map_pow]
      rw [hbase]
  rw [hpoly, translatedOtherRootDenominator]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r hr
  by_cases heq : r = pole
  · simp [heq]
  · simp only [if_neg heq, map_pow, map_add,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
      Polynomial.coe_C]
    ring

theorem otherRootProduct_taylor (ell : ℕ) :
    Polynomial.coeToPowerSeries.ringHom
        ((P.otherRootProduct ell).taylor (-(ell : ℚ))) =
      P.localRootDenominator ell := by
  simpa [localRootDenominator, translatedOtherRootDenominator] using
    P.otherRootProduct_taylorAt ell ell

theorem partialFractionTerm_taylor (h pole center q : ℕ) :
    Polynomial.coeToPowerSeries.ringHom
        ((P.partialFractionTerm h pole q).taylor (-(center : ℚ))) =
      PowerSeries.C (PowerSeries.coeff q (P.localExpansion pole h)) *
        (PowerSeries.C ((pole : ℚ) - (center : ℚ)) + PowerSeries.X) ^ q *
        P.translatedOtherRootDenominator pole center := by
  rw [partialFractionTerm, Polynomial.taylor_mul, Polynomial.taylor_mul,
    Polynomial.taylor_C, Polynomial.taylor_pow]
  simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X]
  have hbase :
      (X + C (pole : ℚ)).taylor (-(center : ℚ)) =
        X + C ((pole : ℚ) - (center : ℚ)) := by
    simp [Polynomial.taylor_apply]
    ring
  rw [hbase]
  simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X,
    Polynomial.coe_C]
  change PowerSeries.C (PowerSeries.coeff q (P.localExpansion pole h)) *
      (PowerSeries.X + PowerSeries.C ((pole : ℚ) - (center : ℚ))) ^ q *
      Polynomial.coeToPowerSeries.ringHom
        ((P.otherRootProduct pole).taylor (-(center : ℚ))) = _
  rw [P.otherRootProduct_taylorAt]
  ring

theorem X_pow_dvd_translatedOtherRootDenominator (pole center : ℕ)
    (hcenter : center ≤ P.n) (hne : center ≠ pole) :
    (PowerSeries.X : PowerSeries ℚ) ^ P.multiplicity center ∣
      P.translatedOtherRootDenominator pole center := by
  classical
  let f : ℕ → PowerSeries ℚ := fun r =>
    if r = pole then 1 else
      (PowerSeries.C ((r : ℚ) - (center : ℚ)) + PowerSeries.X) ^
        P.multiplicity r
  have hm : center ∈ Finset.range (P.n + 1) := by
    simp [hcenter]
  have hsplit := Finset.mul_prod_erase (Finset.range (P.n + 1)) f hm
  have hfactor : f center = (PowerSeries.X : PowerSeries ℚ) ^
      P.multiplicity center := by
    simp [f, hne, sub_self]
  change (PowerSeries.X : PowerSeries ℚ) ^ P.multiplicity center ∣
      ∏ r ∈ Finset.range (P.n + 1), f r
  rw [← hsplit, hfactor]
  exact dvd_mul_right _ _

theorem principalPartTruncation_coeff (ell h j : ℕ)
    (hj : j < P.multiplicity ell) :
    PowerSeries.coeff j (P.principalPartTruncation ell h) =
      PowerSeries.coeff j (P.localExpansion ell h) := by
  classical
  unfold principalPartTruncation
  rw [map_sum]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)]
  · simp [PowerSeries.coeff_C_mul_X_pow]
  · intro q hq hqj
    simp [PowerSeries.coeff_C_mul_X_pow, Ne.symm hqj]

theorem coeff_localExpansion_mul_root_eq_principalPart (ell h j : ℕ)
    (hj : j < P.multiplicity ell) :
    PowerSeries.coeff j
        (P.localExpansion ell h * P.localRootDenominator ell) =
      PowerSeries.coeff j
        (P.principalPartTruncation ell h * P.localRootDenominator ell) := by
  have hdiv : (PowerSeries.X : PowerSeries ℚ) ^ P.multiplicity ell ∣
      P.localExpansion ell h - P.principalPartTruncation ell h := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub]
    rw [P.principalPartTruncation_coeff ell h k hk]
    ring
  have hdiv' : (PowerSeries.X : PowerSeries ℚ) ^ P.multiplicity ell ∣
      (P.localExpansion ell h - P.principalPartTruncation ell h) *
        P.localRootDenominator ell :=
    dvd_mul_of_dvd_left hdiv _
  have hcoeff := (PowerSeries.X_pow_dvd_iff.mp hdiv') j hj
  apply sub_eq_zero.mp
  simpa only [sub_mul, map_sub] using hcoeff

theorem partialFractionNumerator_taylor (h center : ℕ) :
    Polynomial.coeToPowerSeries.ringHom
        ((P.partialFractionNumerator h).taylor (-(center : ℚ))) =
      ∑ pole ∈ Finset.range (P.n + 1),
        ∑ q ∈ Finset.range (P.multiplicity pole),
          PowerSeries.C (PowerSeries.coeff q (P.localExpansion pole h)) *
            (PowerSeries.C ((pole : ℚ) - (center : ℚ)) + PowerSeries.X) ^ q *
            P.translatedOtherRootDenominator pole center := by
  classical
  unfold partialFractionNumerator
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro pole hpole
  apply Finset.sum_congr rfl
  intro q hq
  exact P.partialFractionTerm_taylor h pole center q

theorem partialFractionNumerator_localJet (h ell j : ℕ)
    (hell : ell ≤ P.n) (hj : j < P.multiplicity ell) :
    PowerSeries.coeff j
        (Polynomial.coeToPowerSeries.ringHom
          ((P.partialFractionNumerator h).taylor (-(ell : ℚ)))) =
      PowerSeries.coeff j
        (P.principalPartTruncation ell h * P.localRootDenominator ell) := by
  classical
  rw [P.partialFractionNumerator_taylor]
  rw [map_sum]
  have hellmem : ell ∈ Finset.range (P.n + 1) := by simp [hell]
  rw [Finset.sum_eq_single_of_mem ell hellmem]
  · rw [← Finset.sum_mul]
    have hsum :
        (∑ q ∈ Finset.range (P.multiplicity ell),
          PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h)) *
            (PowerSeries.C ((ell : ℚ) - (ell : ℚ)) + PowerSeries.X) ^ q) =
          P.principalPartTruncation ell h := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [principalPartTruncation, sub_self]
    rw [hsum]
    simp [translatedOtherRootDenominator, localRootDenominator]
  · intro pole hpole hpoleNe
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro q hq
    have hdiv := P.X_pow_dvd_translatedOtherRootDenominator pole ell hell
      (Ne.symm hpoleNe)
    have htermdiv : (PowerSeries.X : PowerSeries ℚ) ^ P.multiplicity ell ∣
        (PowerSeries.C (PowerSeries.coeff q (P.localExpansion pole h)) *
          (PowerSeries.C ((pole : ℚ) - (ell : ℚ)) + PowerSeries.X) ^ q) *
            P.translatedOtherRootDenominator pole ell :=
      dvd_mul_of_dvd_right hdiv _
    exact (PowerSeries.X_pow_dvd_iff.mp htermdiv) j hj

theorem otherRootProduct_natDegree_le (pole : ℕ) (hpole : pole ≤ P.n) :
    (P.otherRootProduct pole).natDegree ≤
      P.totalMultiplicity - P.multiplicity pole := by
  classical
  let S := Finset.range (P.n + 1)
  have hpolemem : pole ∈ S := by
    simp [S, hpole]
  have hsumErase :
      (∑ r ∈ S, if r = pole then 0 else P.multiplicity r) =
        ∑ r ∈ S.erase pole, P.multiplicity r := by
    calc
      _ = ∑ r ∈ S, if r ≠ pole then P.multiplicity r else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases h : r = pole <;> simp [h]
      _ = ∑ r ∈ S.filter (fun r => r ≠ pole), P.multiplicity r := by
            rw [← Finset.sum_filter]
      _ = ∑ r ∈ S.erase pole, P.multiplicity r := by
            congr 1
            ext r
            simp [S, and_comm]
  have htotal : P.totalMultiplicity = P.multiplicity pole +
      ∑ r ∈ S.erase pole, P.multiplicity r := by
    unfold totalMultiplicity
    exact (Finset.add_sum_erase S (fun r => P.multiplicity r) hpolemem).symm
  have hdeg : (P.otherRootProduct pole).natDegree ≤
      ∑ r ∈ S, if r = pole then 0 else P.multiplicity r := by
    unfold otherRootProduct
    calc
      _ ≤ ∑ r ∈ S,
          (if r = pole then 1 else (X + C (r : ℚ)) ^ P.multiplicity r).natDegree :=
            Polynomial.natDegree_prod_le S
              (fun r => if r = pole then 1 else
                (X + C (r : ℚ)) ^ P.multiplicity r)
      _ = _ := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases h : r = pole
            · simp [h]
            · simp only [if_neg h, Polynomial.natDegree_pow,
                Polynomial.natDegree_X_add_C]
              omega
  rw [hsumErase] at hdeg
  rw [htotal]
  omega

theorem multiplicity_le_total (ell : ℕ) :
    P.multiplicity ell ≤ P.totalMultiplicity := by
  have hleM : P.multiplicity ell ≤ M := by
    have hsubset :
        Finset.univ.filter (fun a : Fin M => ell ∈ P.interval a) ⊆ Finset.univ := by
      intro a ha
      simp
    have hcard := Finset.card_le_card hsubset
    simpa [multiplicity] using hcard
  exact hleM.trans P.totalMultiplicity_ge_card

theorem partialFractionTerm_natDegree_lt (h pole q : ℕ)
    (hpole : pole ≤ P.n) (hq : q < P.multiplicity pole) :
    (P.partialFractionTerm h pole q).natDegree < P.totalMultiplicity := by
  have hother := P.otherRootProduct_natDegree_le pole hpole
  have hmain :
      (C (PowerSeries.coeff q (P.localExpansion pole h)) *
          (X + C (pole : ℚ)) ^ q).natDegree ≤ q := by
    calc
      _ ≤ ((X + C (pole : ℚ)) ^ q).natDegree :=
            Polynomial.natDegree_C_mul_le _ _
      _ ≤ q * (X + C (pole : ℚ)).natDegree := Polynomial.natDegree_pow_le
      _ = q := by rw [Polynomial.natDegree_X_add_C]; simp
  have hterm :
      (C (PowerSeries.coeff q (P.localExpansion pole h)) *
          (X + C (pole : ℚ)) ^ q * P.otherRootProduct pole).natDegree ≤
        q + (P.totalMultiplicity - P.multiplicity pole) :=
    Polynomial.natDegree_mul_le.trans (add_le_add hmain hother)
  have hmu := P.multiplicity_le_total pole
  have hstrict : q + (P.totalMultiplicity - P.multiplicity pole) <
      P.totalMultiplicity := by omega
  exact lt_of_le_of_lt (by simpa [partialFractionTerm] using hterm) hstrict

theorem partialFractionNumerator_natDegree_lt (h : ℕ) (hM : 0 < M) :
    (P.partialFractionNumerator h).natDegree < P.totalMultiplicity := by
  classical
  have hNpos : 0 < P.totalMultiplicity := by
    exact lt_of_lt_of_le hM P.totalMultiplicity_ge_card
  have hsumBound : (P.partialFractionNumerator h).natDegree ≤
      P.totalMultiplicity - 1 := by
    unfold partialFractionNumerator
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro pole hpole
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    have hpole' : pole ≤ P.n := by
      have := Finset.mem_range.mp hpole
      omega
    have hterm := P.partialFractionTerm_natDegree_lt h pole q hpole' (Finset.mem_range.mp hq)
    omega
  omega

theorem partialFractionNumerator_eq (h : Fin M) (hM : 0 < M) :
    P.partialFractionNumerator h.val =
      C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) * X ^ h.val := by
  classical
  let f : Polynomial ℚ :=
    C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) * X ^ h.val -
      P.partialFractionNumerator h.val
  have hNsum : (∑ i : Fin (P.n + 1), P.multiplicity i.val) =
      P.totalMultiplicity := by
    simpa [totalMultiplicity] using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ => P.multiplicity i) (P.n + 1))
  have hdegree : f.natDegree < ∑ i : Fin (P.n + 1), P.multiplicity i.val := by
    rw [hNsum]
    have htarget :
        (C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) * X ^ h.val).natDegree <
          P.totalMultiplicity := by
      have hh : h.val < P.totalMultiplicity :=
        lt_of_lt_of_le h.isLt P.totalMultiplicity_ge_card
      exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_X_pow_le _ _) hh
    have hpf := P.partialFractionNumerator_natDegree_lt h.val hM
    dsimp [f]
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt htarget hpf)
  have hnodes : Function.Injective
      (fun i : Fin (P.n + 1) => -(i.val : ℚ)) := by
    intro i k hik
    apply Fin.ext
    have hcast : (i.val : ℚ) = (k.val : ℚ) := neg_injective hik
    exact_mod_cast hcast
  have hjets : ∀ (i : Fin (P.n + 1)) (j : ℕ), j < P.multiplicity i.val →
      (f.taylor (-(i.val : ℚ))).coeff j = 0 := by
    intro i j hj
    have hi : i.val ≤ P.n := by omega
    have htarget :
        Polynomial.coeToPowerSeries.ringHom
          ((C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
            X ^ h.val).taylor (-(i.val : ℚ))) =
          P.localExpansion i.val h.val * P.localRootDenominator i.val := by
      have hpoly :
          (C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) * X ^ h.val).taylor
              (-(i.val : ℚ)) =
            C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
              (X + C (-(i.val : ℚ))) ^ h.val := by
        rw [Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.taylor_pow,
          Polynomial.taylor_X]
      rw [hpoly]
      simp only [Polynomial.coeToPowerSeries.ringHom_apply, map_mul, map_pow,
        Polynomial.coe_C, Polynomial.coe_X]
      rw [P.localExpansion_mul_localRootDenominator]
      simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X,
        Polynomial.coe_C]
      ring_nf
    have hpolyTaylor :
        f.taylor (-(i.val : ℚ)) =
          (C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) * X ^ h.val).taylor
              (-(i.val : ℚ)) -
            (P.partialFractionNumerator h.val).taylor (-(i.val : ℚ)) := by
      dsimp [f]
      exact map_sub (Polynomial.taylor (-(i.val : ℚ))) _ _
    have hcoeffTaylor :
        PowerSeries.coeff j
          (Polynomial.coeToPowerSeries.ringHom (f.taylor (-(i.val : ℚ)))) =
        PowerSeries.coeff j
            (Polynomial.coeToPowerSeries.ringHom
              ((C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
                X ^ h.val).taylor (-(i.val : ℚ)))) -
          PowerSeries.coeff j
            (Polynomial.coeToPowerSeries.ringHom
              ((P.partialFractionNumerator h.val).taylor (-(i.val : ℚ)))) := by
      rw [hpolyTaylor]
      simp only [map_sub]
    have hpoleJet := P.partialFractionNumerator_localJet h.val i.val j hi hj
    have hlocalJet :=
      P.coeff_localExpansion_mul_root_eq_principalPart i.val h.val j hj
    have hvan :
        PowerSeries.coeff j
          (Polynomial.coeToPowerSeries.ringHom (f.taylor (-(i.val : ℚ)))) = 0 := by
      rw [hcoeffTaylor, htarget, hpoleJet, hlocalJet]
      ring
    simpa only [Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeff_coe] using hvan
  have hzero := eq_zero_of_confluent_jets
    (fun i : Fin (P.n + 1) => -(i.val : ℚ)) hnodes
    (fun i => P.multiplicity i.val) f hdegree hjets
  dsimp [f] at hzero
  exact (sub_eq_zero.mp hzero).symm

private theorem reflect_pow_budget (f : Polynomial ℚ) (b k : ℕ)
    (hf : f.natDegree ≤ b) :
    Polynomial.reflect (b * k) (f ^ k) = (Polynomial.reflect b f) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.mul_succ, Polynomial.reflect_mul]
      · rw [ih, pow_succ]
      · calc
          (f ^ k).natDegree ≤ k * f.natDegree := Polynomial.natDegree_pow_le
          _ ≤ k * b := Nat.mul_le_mul_left k hf
          _ = b * k := Nat.mul_comm _ _
      · exact hf

private theorem reflect_pad (f : Polynomial ℚ) {b N : ℕ}
    (hf : f.natDegree ≤ b) (h : b ≤ N) :
    Polynomial.reflect N f = X ^ (N - b) * Polynomial.reflect b f := by
  classical
  ext i
  rw [Polynomial.coeff_reflect, Polynomial.coeff_X_pow_mul']
  by_cases hpad : N - b ≤ i
  · rw [if_pos hpad]
    by_cases hiN : i ≤ N
    · have hk : i - (N - b) ≤ b := by omega
      rw [Polynomial.coeff_reflect]
      change f.coeff (Polynomial.revAt N i) = f.coeff (Polynomial.revAt b (i - (N - b)))
      rw [Polynomial.revAt_le hiN, Polynomial.revAt_le hk]
      congr 1 <;> omega
    · have hiN' : N < i := by omega
      have hk : b < i - (N - b) := by omega
      rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hiN',
        Polynomial.revAt_eq_self_of_lt hk]
      have hzero₁ : f.coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hzero₂ : f.coeff (i - (N - b)) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hzero₁, hzero₂]
  · have hlt : i < N - b := by omega
    rw [if_neg (Nat.not_le.mpr hlt)]
    have hiN : i ≤ N := by omega
    rw [Polynomial.revAt_le hiN]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private theorem reflect_pow_at_budget (f : Polynomial ℚ) (q b : ℕ)
    (hf : f.natDegree ≤ 1) (hqb : q ≤ b) :
    Polynomial.reflect b (f ^ q) =
      X ^ (b - q) * (Polynomial.reflect 1 f) ^ q := by
  have hdeg : (f ^ q).natDegree ≤ q := by
    calc
      (f ^ q).natDegree ≤ q * f.natDegree := Polynomial.natDegree_pow_le
      _ ≤ q * 1 := Nat.mul_le_mul_left q hf
      _ = q := Nat.mul_one q
  rw [reflect_pad (f ^ q) hdeg hqb]
  have hpow := reflect_pow_budget f 1 q hf
  have hpow' : Polynomial.reflect q (f ^ q) = (Polynomial.reflect 1 f) ^ q := by
    simpa using hpow
  rw [hpow']

private theorem reflect_linear (a : ℚ) :
    Polynomial.reflect 1 (X + C a : Polynomial ℚ) = 1 + C a * X := by
  rw [Polynomial.reflect_add]
  simp

private theorem reflect_prod_budget {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Polynomial ℚ) (b : α → ℕ)
    (hf : ∀ a ∈ s, (f a).natDegree ≤ b a) :
    Polynomial.reflect (∑ a ∈ s, b a) (∏ a ∈ s, f a) =
      ∏ a ∈ s, Polynomial.reflect (b a) (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Polynomial.reflect_mul]
      · rw [ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))]
        simp only [Finset.prod_insert ha]
      · exact hf a (Finset.mem_insert_self a s)
      · calc
          (∏ x ∈ s, f x).natDegree ≤ ∑ x ∈ s, (f x).natDegree :=
            Polynomial.natDegree_prod_le s f
          _ ≤ ∑ x ∈ s, b x := Finset.sum_le_sum (fun x hx => hf x (Finset.mem_insert_of_mem hx))

private theorem reflect_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Polynomial ℚ) (N : ℕ) :
    Polynomial.reflect N (∑ a ∈ s, f a) = ∑ a ∈ s, Polynomial.reflect N (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Polynomial.reflect_add, ih, Finset.sum_insert ha]

private theorem reflect_otherRootProduct (ell : ℕ) (hell : ell ≤ P.n) :
    Polynomial.reflect (P.totalMultiplicity - P.multiplicity ell)
        (P.otherRootProduct ell) =
      ∏ r ∈ Finset.range (P.n + 1),
        if r = ell then 1 else
          (1 + C (r : ℚ) * X) ^ P.multiplicity r := by
  classical
  let S := Finset.range (P.n + 1)
  let b : ℕ → ℕ := fun r => if r = ell then 0 else P.multiplicity r
  have hbudget : (∑ r ∈ S, b r) = P.totalMultiplicity - P.multiplicity ell := by
    have hellS : ell ∈ S := by simp [S, hell]
    have hsum : P.multiplicity ell +
        (∑ r ∈ S.erase ell, P.multiplicity r) = P.totalMultiplicity := by
      unfold totalMultiplicity
      exact Finset.add_sum_erase S (fun r => P.multiplicity r) hellS
    have hfilter : S.erase ell = S.filter (fun r => r ≠ ell) := by
      ext r
      simp [and_comm]
    have herase : (∑ r ∈ S.erase ell, P.multiplicity r) = ∑ r ∈ S, b r := by
      rw [hfilter]
      simp [Finset.sum_filter, b]
    rw [← herase]
    omega
  have hprod : ∀ r ∈ S,
      (if r = ell then (1 : Polynomial ℚ) else
        (X + C (r : ℚ)) ^ P.multiplicity r).natDegree ≤ b r := by
    intro r hr
    by_cases h : r = ell
    · simp [h, b]
    · have hb : b r = P.multiplicity r := by simp [b, h]
      rw [if_neg h, hb]
      calc
        ((X + C (r : ℚ)) ^ P.multiplicity r).natDegree ≤
            P.multiplicity r * (X + C (r : ℚ)).natDegree :=
              Polynomial.natDegree_pow_le
        _ = P.multiplicity r := by rw [Polynomial.natDegree_X_add_C]; omega
  have hreflect := reflect_prod_budget S
    (fun r => if r = ell then (1 : Polynomial ℚ) else
      (X + C (r : ℚ)) ^ P.multiplicity r) b hprod
  change Polynomial.reflect (P.totalMultiplicity - P.multiplicity ell)
      (∏ r ∈ S, if r = ell then (1 : Polynomial ℚ) else
        (X + C (r : ℚ)) ^ P.multiplicity r) = _
  rw [← hbudget, hreflect]
  apply Finset.prod_congr rfl
  intro r hr
  by_cases h : r = ell
  · simp [h, b]
  · have hpow := reflect_pow_at_budget (X + C (r : ℚ))
      (P.multiplicity r) (P.multiplicity r)
      (by rw [Polynomial.natDegree_X_add_C]) le_rfl
    rw [reflect_linear] at hpow
    simpa [b, h, reflect_linear] using hpow

private theorem reflect_partialFractionTerm (h ell q : ℕ)
    (hell : ell ≤ P.n) (hq : q < P.multiplicity ell) :
    Polynomial.reflect P.totalMultiplicity (P.partialFractionTerm h ell q) =
      C (PowerSeries.coeff q (P.localExpansion ell h)) *
        X ^ (P.multiplicity ell - q) *
        (1 + C (ell : ℚ) * X) ^ q *
        ∏ r ∈ Finset.range (P.n + 1),
          if r = ell then 1 else
            (1 + C (r : ℚ) * X) ^ P.multiplicity r := by
  have hmu : P.multiplicity ell ≤ P.totalMultiplicity :=
    P.multiplicity_le_total ell
  let f := C (PowerSeries.coeff q (P.localExpansion ell h)) *
    (X + C (ell : ℚ)) ^ q
  have hf : f.natDegree ≤ P.multiplicity ell := by
    dsimp [f]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by
      calc
        ((X + C (ell : ℚ)) ^ q).natDegree ≤ q * (X + C (ell : ℚ)).natDegree :=
            Polynomial.natDegree_pow_le
        _ = q := by rw [Polynomial.natDegree_X_add_C]; omega
        _ ≤ P.multiplicity ell := Nat.le_of_lt hq)
  have hmul := Polynomial.reflect_mul f (P.otherRootProduct ell) hf
    (P.otherRootProduct_natDegree_le ell hell)
  unfold partialFractionTerm
  change Polynomial.reflect P.totalMultiplicity
      ((C (PowerSeries.coeff q (P.localExpansion ell h)) *
        (X + C (ell : ℚ)) ^ q) * P.otherRootProduct ell) = _
  rw [← Nat.add_sub_of_le hmu, hmul, Polynomial.reflect_C_mul,
    reflect_pow_at_budget (X + C (ell : ℚ)) q (P.multiplicity ell)
      (by rw [Polynomial.natDegree_X_add_C]) (Nat.le_of_lt hq),
    reflect_linear, P.reflect_otherRootProduct ell hell]
  ring

theorem partialFractionNumerator_reflect_sum (h : Fin M) (hM : 0 < M) :
    (∑ ell ∈ Finset.range (P.n + 1),
      ∑ q ∈ Finset.range (P.multiplicity ell),
        C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
          X ^ (P.multiplicity ell - q) *
          (1 + C (ell : ℚ) * X) ^ q *
          ∏ r ∈ Finset.range (P.n + 1),
            if r = ell then 1 else
              (1 + C (r : ℚ) * X) ^ P.multiplicity r) =
      C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
        X ^ (P.totalMultiplicity - h.val) := by
  classical
  have hD : h.val ≤ P.totalMultiplicity :=
    (Nat.lt_of_lt_of_le h.isLt P.totalMultiplicity_ge_card).le
  have hglobal := congrArg (Polynomial.reflect P.totalMultiplicity)
    (P.partialFractionNumerator_eq h hM)
  rw [Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_le hD] at hglobal
  have hsplit :
      Polynomial.reflect P.totalMultiplicity (P.partialFractionNumerator h.val) =
        ∑ ell ∈ Finset.range (P.n + 1),
          ∑ q ∈ Finset.range (P.multiplicity ell),
            Polynomial.reflect P.totalMultiplicity
              (P.partialFractionTerm h.val ell q) := by
    change Polynomial.reflect P.totalMultiplicity
        (∑ ell ∈ Finset.range (P.n + 1),
          ∑ q ∈ Finset.range (P.multiplicity ell),
            P.partialFractionTerm h.val ell q) = _
    rw [reflect_sum]
    apply Finset.sum_congr rfl
    intro ell hell
    exact reflect_sum _ _ _
  have hterms :
      (∑ ell ∈ Finset.range (P.n + 1),
        ∑ q ∈ Finset.range (P.multiplicity ell),
          Polynomial.reflect P.totalMultiplicity
            (P.partialFractionTerm h.val ell q)) =
        (∑ ell ∈ Finset.range (P.n + 1),
          ∑ q ∈ Finset.range (P.multiplicity ell),
            C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
              X ^ (P.multiplicity ell - q) *
              (1 + C (ell : ℚ) * X) ^ q *
              ∏ r ∈ Finset.range (P.n + 1),
                if r = ell then 1 else
                  (1 + C (r : ℚ) * X) ^ P.multiplicity r) := by
    apply Finset.sum_congr rfl
    intro ell hell
    apply Finset.sum_congr rfl
    intro q hq
    exact P.reflect_partialFractionTerm h.val ell q
      (by have := Finset.mem_range.mp hell; omega)
      (Finset.mem_range.mp hq)
  rw [hsplit] at hglobal
  rw [hterms] at hglobal
  exact hglobal

/-- A reversed linear factor at the root indexed by `ell`. -/
noncomputable def reversedRootFactor (ell : ℕ) : PowerSeries ℚ :=
  1 + PowerSeries.C (ell : ℚ) * PowerSeries.X

/-- The denominator after the substitution `z = 1/X` and clearing its total
power of `X`. -/
noncomputable def reversedRootDenominator : PowerSeries ℚ :=
  ∏ ell ∈ Finset.range (P.n + 1),
    (reversedRootFactor ell) ^ P.multiplicity ell

/-- The product of the reversed factors away from a selected pole. -/
noncomputable def reversedOtherRootProduct (ell : ℕ) : PowerSeries ℚ :=
  ∏ r ∈ Finset.range (P.n + 1),
    if r = ell then 1 else (reversedRootFactor r) ^ P.multiplicity r

/-- The inverse of a repeated reversed root factor, represented by the
rescaled negative-binomial series. -/
noncomputable def reversedReciprocal (ell k : ℕ) : PowerSeries ℚ :=
  PowerSeries.rescale (-(ell : ℚ))
    (PowerSeries.invOneSubPow ℚ k).val

/-- One ordinary partial-fraction term at infinity. -/
noncomputable def reversedPartialFractionTerm (h ell q : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h)) *
    PowerSeries.X ^ (P.multiplicity ell - q) *
    reversedReciprocal ell (P.multiplicity ell - q)

/-- The complete finite partial-fraction expansion at infinity. -/
noncomputable def reversedPartialFractionSeries (h : ℕ) : PowerSeries ℚ :=
  ∑ ell ∈ Finset.range (P.n + 1),
    ∑ q ∈ Finset.range (P.multiplicity ell),
      P.reversedPartialFractionTerm h ell q

private theorem powerSeries_natCast_eq_C (k : ℕ) :
    (k : PowerSeries ℚ) = PowerSeries.C (k : ℚ) := by
  exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) k).symm

private theorem coe_reversedRootFactor_pow (ell q : ℕ) :
    (((1 + C (ell : ℚ) * X) ^ q : Polynomial ℚ) : PowerSeries ℚ) =
      (1 + PowerSeries.C (ell : ℚ) * PowerSeries.X) ^ q := by
  simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]

/-- The exponential jet sum for one row, with the actual column indexing. -/
noncomputable def exponentialLocalJetCombination (h : ℕ) : PowerSeries ℚ :=
  ∑ ell ∈ Finset.range (P.n + 1),
    ∑ j ∈ Finset.range M,
      PowerSeries.C (P.localCoefficient ell h j / (Nat.factorial j : ℚ)) *
        PowerSeries.X ^ j * PowerSeries.rescale (-(ell : ℚ)) (PowerSeries.exp ℚ)

/-- Shifted exponential Borel transform: the coefficient of degree `k` is
the coefficient of degree `k+1`, divided by `k!`. -/
noncomputable def factorialBorelShift (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => f.coeff (k + 1) / (Nat.factorial k : ℚ)

@[simp]
theorem coeff_factorialBorelShift (f : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (factorialBorelShift f) =
      f.coeff (k + 1) / (Nat.factorial k : ℚ) := by
  simp [factorialBorelShift]

theorem factorialBorelShift_add (f g : PowerSeries ℚ) :
    factorialBorelShift (f + g) = factorialBorelShift f + factorialBorelShift g := by
  ext k
  simp [factorialBorelShift, add_div]

theorem factorialBorelShift_sum {α : Type*} (s : Finset α)
    (f : α → PowerSeries ℚ) :
    factorialBorelShift (∑ a ∈ s, f a) =
      ∑ a ∈ s, factorialBorelShift (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext k; simp [factorialBorelShift]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, factorialBorelShift_add, ih,
        Finset.sum_insert ha]

theorem factorialBorelShift_C_mul (c : ℚ) (f : PowerSeries ℚ) :
    factorialBorelShift (PowerSeries.C c * f) =
      PowerSeries.C c * factorialBorelShift f := by
  ext k
  simp [factorialBorelShift, div_eq_mul_inv, mul_assoc, mul_left_comm]

theorem factorialBorelShift_X_pow_mul_dvd {f : PowerSeries ℚ} {n : ℕ}
    (hn : 0 < n) (hdiv : PowerSeries.X ^ n ∣ f) :
    PowerSeries.X ^ (n - 1) ∣ factorialBorelShift f := by
  rw [PowerSeries.X_pow_dvd_iff] at hdiv ⊢
  intro k hk
  rw [coeff_factorialBorelShift]
  have hcoeff := hdiv (k + 1) (by omega)
  rw [hcoeff]
  simp

theorem reversedReciprocal_coeff (ell j n : ℕ) :
    PowerSeries.coeff n (reversedReciprocal ell (j + 1)) =
      (-(ell : ℚ)) ^ n * (Nat.choose (j + n) j : ℚ) := by
  rw [reversedReciprocal, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp [PowerSeries.coeff_mk]

private theorem choose_factorial_ratio (j n : ℕ) (hjn : j ≤ n) :
    (Nat.choose n j : ℚ) / (Nat.factorial n : ℚ) =
      1 / ((Nat.factorial j : ℚ) * (Nat.factorial (n - j) : ℚ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial hjn
  have hq : (Nat.choose n j : ℚ) * (Nat.factorial j : ℚ) *
      (Nat.factorial (n - j) : ℚ) = (Nat.factorial n : ℚ) := by
    exact_mod_cast hnat
  have hj : (Nat.factorial j : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hm : (Nat.factorial (n - j) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - j)
  have hn : (Nat.factorial n : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hj, hm, hn] at hq ⊢ <;> nlinarith

theorem factorialBorelShift_monomial_reciprocal (ell j : ℕ) :
    factorialBorelShift
        (PowerSeries.X ^ (j + 1) * reversedReciprocal ell (j + 1)) =
      PowerSeries.C (1 / (Nat.factorial j : ℚ)) * PowerSeries.X ^ j *
        PowerSeries.rescale (-(ell : ℚ)) (PowerSeries.exp ℚ) := by
  ext n
  by_cases hjn : j ≤ n
  · have hk : j + 1 ≤ n + 1 := by omega
    have hcoeff := reversedReciprocal_coeff ell j (n - j)
    let m := n - j
    rw [coeff_factorialBorelShift, PowerSeries.coeff_X_pow_mul']
    simp only [hk, ↓reduceIte]
    have hidx : n + 1 - (j + 1) = n - j := by omega
    rw [hidx, hcoeff]
    have hsum : j + (n - j) = n := Nat.add_sub_of_le hjn
    rw [hsum]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp only [hjn, ↓reduceIte, PowerSeries.coeff_rescale,
      PowerSeries.coeff_exp]
    have hratio := choose_factorial_ratio j n hjn
    calc
      (-(ell : ℚ)) ^ m * (Nat.choose n j : ℚ) /
          (Nat.factorial n : ℚ) =
        (-(ell : ℚ)) ^ m *
          (1 / ((Nat.factorial j : ℚ) * (Nat.factorial m : ℚ))) := by
            rw [← hratio]
            ring
      _ = 1 / (Nat.factorial j : ℚ) *
            ((-(ell : ℚ)) ^ m * (1 / (Nat.factorial m : ℚ))) := by
            field_simp [Nat.factorial_ne_zero j, Nat.factorial_ne_zero m]
  · have hk : ¬ j + 1 ≤ n + 1 := by omega
    rw [coeff_factorialBorelShift, PowerSeries.coeff_X_pow_mul']
    simp only [hk, ↓reduceIte]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp [hjn]

private noncomputable def exponentialLocalJetTerm (ell h j : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (P.localCoefficient ell h j / (Nat.factorial j : ℚ)) *
    PowerSeries.X ^ j * PowerSeries.rescale (-(ell : ℚ)) (PowerSeries.exp ℚ)

private theorem multiplicity_le_M (ell : ℕ) : P.multiplicity ell ≤ M := by
  have hs : (Finset.univ.filter (fun a : Fin M => ell ∈ P.interval a)) ⊆
      Finset.univ := by
    intro a ha
    simp
  have hcard := Finset.card_le_card hs
  simpa [ActualIntervals.multiplicity] using hcard

theorem factorialBorelShift_reversedPartialFractionSeries (h : ℕ) :
    factorialBorelShift (P.reversedPartialFractionSeries h) =
      P.exponentialLocalJetCombination h := by
  classical
  unfold reversedPartialFractionSeries
  rw [factorialBorelShift_sum]
  unfold exponentialLocalJetCombination
  apply Finset.sum_congr rfl
  intro ell hell
  let μ := P.multiplicity ell
  have hμM : μ ≤ M := by dsimp [μ]; exact P.multiplicity_le_M ell
  let f : ℕ → PowerSeries ℚ := fun j =>
    PowerSeries.C (PowerSeries.coeff (μ - 1 - j) (P.localExpansion ell h) /
      (Nat.factorial j : ℚ)) * PowerSeries.X ^ j *
      PowerSeries.rescale (-(ell : ℚ)) (PowerSeries.exp ℚ)
  let g : ℕ → PowerSeries ℚ := fun j => P.exponentialLocalJetTerm ell h j
  have hreflect :
      (∑ q ∈ Finset.range μ, f (μ - 1 - q)) =
        ∑ j ∈ Finset.range μ, f j := by
    simpa [f] using Finset.sum_range_reflect f μ
  have hsmall : (∑ j ∈ Finset.range μ, g j) =
      ∑ j ∈ Finset.range μ, f j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < μ := Finset.mem_range.mp hj
    have hlocal : P.localCoefficient ell h j =
        PowerSeries.coeff (μ - 1 - j) (P.localExpansion ell h) := by
      simp [ActualIntervals.localCoefficient, hjlt, μ]
    simp [g, f, exponentialLocalJetTerm, hlocal]
  have hlarge : (∑ j ∈ Finset.range μ, g j) =
      ∑ j ∈ Finset.range M, g j := by
    apply Finset.sum_subset (Finset.range_mono hμM)
    intro j hjM hjμ
    have hjltM : j < M := Finset.mem_range.mp hjM
    have hjge : μ ≤ j := by
      have hnmem : ¬ j < μ := by simpa using hjμ
      omega
    have hnot : ¬ j < P.multiplicity ell := by omega
    have hlocal : P.localCoefficient ell h j = 0 := by
      rw [ActualIntervals.localCoefficient, if_neg hnot]
    simp [g, exponentialLocalJetTerm, hlocal]
  have hqterm : ∀ q ∈ Finset.range μ,
      factorialBorelShift (P.reversedPartialFractionTerm h ell q) =
        f (μ - 1 - q) := by
    intro q hq
    have hqμ : q < μ := Finset.mem_range.mp hq
    let j := μ - 1 - q
    have hjlt : j < μ := by dsimp [j]; omega
    have hjplus : j + 1 = μ - q := by dsimp [j]; omega
    have hidx : μ - 1 - (μ - 1 - q) = q := by omega
    unfold reversedPartialFractionTerm
    rw [← hjplus, mul_assoc, factorialBorelShift_C_mul,
      factorialBorelShift_monomial_reciprocal]
    simp [f, j, hidx, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    factorialBorelShift
        (∑ q ∈ Finset.range μ, P.reversedPartialFractionTerm h ell q) =
      ∑ q ∈ Finset.range μ,
        factorialBorelShift (P.reversedPartialFractionTerm h ell q) := by
          rw [factorialBorelShift_sum]
    _ = ∑ q ∈ Finset.range μ, f (μ - 1 - q) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact hqterm q hq
    _ = ∑ j ∈ Finset.range μ, f j := hreflect
    _ = ∑ j ∈ Finset.range μ, g j := hsmall.symm
    _ = ∑ j ∈ Finset.range M, g j := hlarge

theorem reversedReciprocal_mul_factor_pow (ell k : ℕ) :
    reversedReciprocal ell k * (reversedRootFactor ell) ^ k = 1 := by
  have hbase : (PowerSeries.invOneSubPow ℚ k).val *
      (1 - PowerSeries.X) ^ k = 1 := by
    have h := (PowerSeries.invOneSubPow ℚ k).val_inv
    simpa only [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] using h
  have hlinear : PowerSeries.rescale (-(ell : ℚ))
      (1 - PowerSeries.X) = reversedRootFactor ell := by
    simp [reversedRootFactor, PowerSeries.rescale_X]
  have h := congrArg (PowerSeries.rescale (-(ell : ℚ))) hbase
  simpa [reversedReciprocal, hlinear] using h

private theorem reversedOtherRootProduct_eq_erase (ell : ℕ)
    (hell : ell ≤ P.n) :
    P.reversedOtherRootProduct ell =
      ∏ r ∈ (Finset.range (P.n + 1)).erase ell,
        (reversedRootFactor r) ^ P.multiplicity r := by
  classical
  let S := Finset.range (P.n + 1)
  let f : ℕ → PowerSeries ℚ := fun r =>
    if r = ell then 1 else (reversedRootFactor r) ^ P.multiplicity r
  have hunit : f ell = 1 := by simp [f]
  have herase := Finset.prod_erase (s := S) (f := f) (a := ell) hunit
  have hfilter : ∀ r ∈ S.erase ell,
      f r = (reversedRootFactor r) ^ P.multiplicity r := by
    intro r hr
    simp [f, Finset.mem_erase.mp hr]
  calc
    P.reversedOtherRootProduct ell = ∏ r ∈ S, f r := rfl
    _ = ∏ r ∈ S.erase ell, f r := herase.symm
    _ = ∏ r ∈ S.erase ell, (reversedRootFactor r) ^ P.multiplicity r := by
      apply Finset.prod_congr rfl
      intro r hr
      exact hfilter r hr

theorem reversedRootDenominator_eq_factor_mul_other (ell : ℕ)
    (hell : ell ≤ P.n) :
    P.reversedRootDenominator =
      (reversedRootFactor ell) ^ P.multiplicity ell *
        P.reversedOtherRootProduct ell := by
  classical
  let S := Finset.range (P.n + 1)
  have hellS : ell ∈ S := by simp [S, hell]
  have hsplit := Finset.mul_prod_erase S
    (fun r => (reversedRootFactor r) ^ P.multiplicity r) hellS
  rw [reversedRootDenominator, ← hsplit, P.reversedOtherRootProduct_eq_erase ell hell]

theorem reversedReciprocal_mul_factor_pow_add (ell k q : ℕ) :
    reversedReciprocal ell k * (reversedRootFactor ell) ^ (k + q) =
      (reversedRootFactor ell) ^ q := by
  rw [pow_add]
  calc
    reversedReciprocal ell k *
          ((reversedRootFactor ell) ^ k * (reversedRootFactor ell) ^ q) =
        (reversedReciprocal ell k * (reversedRootFactor ell) ^ k) *
          (reversedRootFactor ell) ^ q := by ring
    _ = (reversedRootFactor ell) ^ q := by
      rw [reversedReciprocal_mul_factor_pow]
      simp

theorem reversedPartialFractionTerm_mul_denominator (h ell q : ℕ)
    (hell : ell ≤ P.n) (hq : q < P.multiplicity ell) :
    P.reversedPartialFractionTerm h ell q * P.reversedRootDenominator =
      PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h)) *
        PowerSeries.X ^ (P.multiplicity ell - q) *
        (reversedRootFactor ell) ^ q * P.reversedOtherRootProduct ell := by
  let k := P.multiplicity ell - q
  have hsum : k + q = P.multiplicity ell := by dsimp [k]; omega
  rw [reversedPartialFractionTerm, P.reversedRootDenominator_eq_factor_mul_other ell hell]
  have hcancel := reversedReciprocal_mul_factor_pow_add ell k q
  have hfactorpow : (reversedRootFactor ell) ^ P.multiplicity ell =
      (reversedRootFactor ell) ^ (k + q) := by rw [← hsum]
  rw [hfactorpow]
  calc
    _ = PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h)) *
          PowerSeries.X ^ k *
          (reversedReciprocal ell k *
            (reversedRootFactor ell) ^ (k + q)) *
          P.reversedOtherRootProduct ell := by
          dsimp [k]
          ring
    _ = PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h)) *
          PowerSeries.X ^ k * (reversedRootFactor ell) ^ q *
          P.reversedOtherRootProduct ell := by rw [hcancel]
    _ = _ := by rfl

theorem reversedPartialFractionSeries_mul_denominator (h : Fin M) (hM : 0 < M) :
    P.reversedPartialFractionSeries h.val * P.reversedRootDenominator =
      PowerSeries.C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
        PowerSeries.X ^ (P.totalMultiplicity - h.val) := by
  classical
  let S := Finset.range (P.n + 1)
  have htermSum :
      (∑ ell ∈ S, ∑ q ∈ Finset.range (P.multiplicity ell),
        P.reversedPartialFractionTerm h.val ell q * P.reversedRootDenominator) =
      (∑ ell ∈ S, ∑ q ∈ Finset.range (P.multiplicity ell),
        PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
          PowerSeries.X ^ (P.multiplicity ell - q) *
          (1 + PowerSeries.C (ell : ℚ) * PowerSeries.X) ^ q *
          ∏ r ∈ S, if r = ell then 1 else
            (1 + PowerSeries.C (r : ℚ) * PowerSeries.X) ^ P.multiplicity r) := by
    apply Finset.sum_congr rfl
    intro ell hell
    apply Finset.sum_congr rfl
    intro q hq
    have helln : ell ≤ P.n := by
      have := Finset.mem_range.mp hell
      omega
    have hcancel := P.reversedPartialFractionTerm_mul_denominator h.val ell q
      helln (Finset.mem_range.mp hq)
    simpa [reversedRootFactor, reversedOtherRootProduct, S] using
      hcancel
  have hpoly := congrArg Polynomial.coeToPowerSeries.ringHom
    (P.partialFractionNumerator_reflect_sum h hM)
  have hrootFactorMap (ell r : ℕ) :
      Polynomial.coeToPowerSeries.ringHom
          (if r = ell then (1 : Polynomial ℚ) else
            (1 + C (r : ℚ) * X) ^ P.multiplicity r) =
        if r = ell then (1 : PowerSeries ℚ) else
          (1 + PowerSeries.C (r : ℚ) * PowerSeries.X) ^ P.multiplicity r := by
    by_cases hr : r = ell
    · simp [hr]
    · rw [if_neg hr, if_neg hr, map_pow,
        Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_X]
  have hproductMap (ell : ℕ) :
      Polynomial.coeToPowerSeries.ringHom
          (∏ r ∈ S, if r = ell then (1 : Polynomial ℚ) else
            (1 + C (r : ℚ) * X) ^ P.multiplicity r) =
        ∏ r ∈ S, if r = ell then (1 : PowerSeries ℚ) else
          (1 + PowerSeries.C (r : ℚ) * PowerSeries.X) ^ P.multiplicity r := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro r hr
    exact hrootFactorMap ell r
  have htermMap (ell q : ℕ) :
      Polynomial.coeToPowerSeries.ringHom
          (C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
            X ^ (P.multiplicity ell - q) *
            (1 + C (ell : ℚ) * X) ^ q *
            ∏ r ∈ S, if r = ell then (1 : Polynomial ℚ) else
              (1 + C (r : ℚ) * X) ^ P.multiplicity r) =
        PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
          PowerSeries.X ^ (P.multiplicity ell - q) *
          (1 + PowerSeries.C (ell : ℚ) * PowerSeries.X) ^ q *
          ∏ r ∈ S, if r = ell then (1 : PowerSeries ℚ) else
            (1 + PowerSeries.C (r : ℚ) * PowerSeries.X) ^ P.multiplicity r := by
    simp only [map_mul, map_pow, hproductMap, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X, map_add, map_one]
  have hsumMap :
      Polynomial.coeToPowerSeries.ringHom
          (∑ ell ∈ S, ∑ q ∈ Finset.range (P.multiplicity ell),
            C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
              X ^ (P.multiplicity ell - q) *
              (1 + C (ell : ℚ) * X) ^ q *
              ∏ r ∈ S, if r = ell then (1 : Polynomial ℚ) else
                (1 + C (r : ℚ) * X) ^ P.multiplicity r) =
        ∑ ell ∈ S, ∑ q ∈ Finset.range (P.multiplicity ell),
          PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
            PowerSeries.X ^ (P.multiplicity ell - q) *
            (1 + PowerSeries.C (ell : ℚ) * PowerSeries.X) ^ q *
            ∏ r ∈ S, if r = ell then (1 : PowerSeries ℚ) else
              (1 + PowerSeries.C (r : ℚ) * PowerSeries.X) ^ P.multiplicity r := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ell hell
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact htermMap ell q
  have hpolySeries :
      (∑ ell ∈ S, ∑ q ∈ Finset.range (P.multiplicity ell),
        PowerSeries.C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
          PowerSeries.X ^ (P.multiplicity ell - q) *
          (1 + PowerSeries.C (ell : ℚ) * PowerSeries.X) ^ q *
          ∏ r ∈ S, if r = ell then 1 else
            (1 + PowerSeries.C (r : ℚ) * PowerSeries.X) ^ P.multiplicity r) =
      PowerSeries.C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
        PowerSeries.X ^ (P.totalMultiplicity - h.val) := by
    have hpolyS :
        Polynomial.coeToPowerSeries.ringHom
            (∑ ell ∈ S, ∑ q ∈ Finset.range (P.multiplicity ell),
              C (PowerSeries.coeff q (P.localExpansion ell h.val)) *
                X ^ (P.multiplicity ell - q) *
                (1 + C (ell : ℚ) * X) ^ q *
                ∏ r ∈ S, if r = ell then (1 : Polynomial ℚ) else
                  (1 + C (r : ℚ) * X) ^ P.multiplicity r) =
          Polynomial.coeToPowerSeries.ringHom
            (C (∏ a : Fin M, (Nat.factorial (P.length a) : ℚ)) *
              X ^ (P.totalMultiplicity - h.val)) := by
      simpa [S] using hpoly
    rw [hsumMap] at hpolyS
    simpa only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X] using hpolyS
  unfold reversedPartialFractionSeries
  calc
    _ = ∑ ell ∈ S, ∑ q ∈ Finset.range (P.multiplicity ell),
          P.reversedPartialFractionTerm h.val ell q * P.reversedRootDenominator := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ell hell
          rw [Finset.sum_mul]
    _ = _ := htermSum
    _ = _ := hpolySeries

theorem reversedRootDenominator_constantCoeff :
    PowerSeries.coeff 0 P.reversedRootDenominator = 1 := by
  simp [reversedRootDenominator, reversedRootFactor]

theorem reversedPartialFractionSeries_dvd (h : Fin M) (hM : 0 < M) :
    PowerSeries.X ^ (P.totalMultiplicity - h.val) ∣
      P.reversedPartialFractionSeries h.val := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  have hprod := P.reversedPartialFractionSeries_mul_denominator h hM
  have hvan : ∀ j, j < P.totalMultiplicity - h.val →
      PowerSeries.coeff j
        (P.reversedRootDenominator * P.reversedPartialFractionSeries h.val) = 0 := by
    intro j hj
    rw [← mul_comm, hprod]
    rw [PowerSeries.coeff_C_mul_X_pow]
    split_ifs with heq
    · omega
    · rfl
  have hD0 : PowerSeries.coeff 0 P.reversedRootDenominator ≠ 0 := by
    rw [P.reversedRootDenominator_constantCoeff]
    norm_num
  have hjet := (unit_mul_jets_iff P.reversedRootDenominator
    (P.reversedPartialFractionSeries h.val) (P.totalMultiplicity - h.val) hD0).mp
      hvan
  exact hjet j hj

theorem exponentialLocalJetCombination_dvd (h : Fin M) (hM : 0 < M)
    (r : ℕ) (hr : r + 1 ≤ P.totalMultiplicity - h.val) :
    PowerSeries.X ^ r ∣ P.exponentialLocalJetCombination h.val := by
  have hkpos : 0 < P.totalMultiplicity - h.val := by omega
  have hshift := factorialBorelShift_X_pow_mul_dvd hkpos
    (P.reversedPartialFractionSeries_dvd h hM)
  rw [P.factorialBorelShift_reversedPartialFractionSeries h.val] at hshift
  have hpow : (PowerSeries.X : PowerSeries ℚ) ^ r ∣
      (PowerSeries.X : PowerSeries ℚ) ^ (P.totalMultiplicity - h.val - 1) := by
    have hrle : r ≤ P.totalMultiplicity - h.val - 1 := by omega
    refine ⟨(PowerSeries.X : PowerSeries ℚ) ^
      (P.totalMultiplicity - h.val - 1 - r), ?_⟩
    have hexp : r + (P.totalMultiplicity - h.val - 1 - r) =
        P.totalMultiplicity - h.val - 1 := Nat.add_sub_of_le hrle
    calc
      (PowerSeries.X : PowerSeries ℚ) ^ (P.totalMultiplicity - h.val - 1) =
        (PowerSeries.X : PowerSeries ℚ) ^
          (r + (P.totalMultiplicity - h.val - 1 - r)) :=
            congrArg (fun k : ℕ => (PowerSeries.X : PowerSeries ℚ) ^ k) hexp.symm
      _ = (PowerSeries.X : PowerSeries ℚ) ^ r *
          (PowerSeries.X : PowerSeries ℚ) ^
            (P.totalMultiplicity - h.val - 1 - r) :=
              pow_add (PowerSeries.X : PowerSeries ℚ) r
                (P.totalMultiplicity - h.val - 1 - r)
  exact dvd_trans hpow hshift

end ActualIntervals

/-- The normalization `m! d^m / j!`, where `m=M-1`. -/
noncomputable def auxiliaryScale (M n j : ℕ) : ℚ :=
  ((Nat.factorial (M - 1) : ℕ) : ℚ) *
    (intervalLcm n : ℚ) ^ (M - 1) / (Nat.factorial j : ℚ)

/-- The common numerator of all column normalizations. -/
noncomputable def auxiliaryCommonScale (M n : ℕ) : ℚ :=
  ((Nat.factorial (M - 1) : ℕ) : ℚ) *
    (intervalLcm n : ℚ) ^ (M - 1)

theorem auxiliaryScale_mul_factorial (M n j : ℕ) :
    auxiliaryScale M n j * (Nat.factorial j : ℚ) = auxiliaryCommonScale M n := by
  unfold auxiliaryScale auxiliaryCommonScale
  field_simp [Nat.factorial_ne_zero j]

theorem auxiliaryCommonScale_ne_zero (M n : ℕ) :
    auxiliaryCommonScale M n ≠ 0 := by
  unfold auxiliaryCommonScale
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero (M - 1)
  · apply pow_ne_zero
    exact_mod_cast ne_of_gt (intervalLcm_pos n)

theorem auxiliaryScale_mul_commonScale_inv (M n j : ℕ) :
    auxiliaryScale M n j * (auxiliaryCommonScale M n)⁻¹ =
      (Nat.factorial j : ℚ)⁻¹ := by
  have hj : (Nat.factorial j : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hC := auxiliaryCommonScale_ne_zero M n
  field_simp [hj, hC]
  nlinarith [auxiliaryScale_mul_factorial M n j]

/-- The actual finite auxiliary coefficient polynomial, presented through the
local partial-fraction coefficients. -/
noncomputable def actualAuxiliary (P : ActualIntervals M) (h j : Fin M) : Polynomial ℚ :=
  ∑ ell ∈ Finset.range (P.n + 1),
    C (auxiliaryScale M P.n j * P.localCoefficient ell h j) * X ^ (P.n - ell)

/-- The actual auxiliary polynomial evaluated at the formal exponential. -/
noncomputable def actualAuxiliaryAtExp (P : ActualIntervals M) (h j : Fin M) :
    PowerSeries ℚ :=
  Polynomial.eval₂ PowerSeries.C (PowerSeries.exp ℚ) (actualAuxiliary P h j)

/-- The matrix of exponential evaluations, used only to extract the common
high-order row relation. -/
noncomputable def actualAuxiliaryExpMatrix (P : ActualIntervals M) :
    Matrix (Fin M) (Fin M) (PowerSeries ℚ) :=
  fun h j => actualAuxiliaryAtExp P h j

/-- The column relation vector with entries `X^j / C₀`. -/
noncomputable def auxiliaryJetVector (M n : ℕ) (j : Fin M) : PowerSeries ℚ :=
  PowerSeries.C (auxiliaryCommonScale M n)⁻¹ * PowerSeries.X ^ j.val

theorem actualAuxiliaryAtExp_eq_sum (P : ActualIntervals M) (h j : Fin M) :
    actualAuxiliaryAtExp P h j =
      ∑ ell ∈ Finset.range (P.n + 1),
        PowerSeries.C (auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val) *
          PowerSeries.exp ℚ ^ (P.n - ell) := by
  rw [actualAuxiliaryAtExp, actualAuxiliary, Polynomial.eval₂_finsetSum]
  simp [Polynomial.eval₂_C, Polynomial.eval₂_X]

theorem exp_pow_mul_rescale_neg (n ell : ℕ) (hell : ell ≤ n) :
    PowerSeries.exp ℚ ^ n * PowerSeries.rescale (-(ell : ℚ)) (PowerSeries.exp ℚ) =
      PowerSeries.exp ℚ ^ (n - ell) := by
  calc
    _ = PowerSeries.rescale (n : ℚ) (PowerSeries.exp ℚ) *
          PowerSeries.rescale (-(ell : ℚ)) (PowerSeries.exp ℚ) := by
            rw [← PowerSeries.exp_pow_eq_rescale_exp]
    _ = PowerSeries.rescale ((n : ℚ) + (-(ell : ℚ))) (PowerSeries.exp ℚ) :=
          PowerSeries.exp_mul_exp_eq_exp_add _ _
    _ = PowerSeries.rescale ((n - ell : ℕ) : ℚ) (PowerSeries.exp ℚ) := by
          congr 1
          have hcast : ((n - ell : ℕ) : ℚ) = (n : ℚ) - ell := by
            rw [Nat.cast_sub hell]
          rw [hcast]
          ring
    _ = PowerSeries.exp ℚ ^ (n - ell) :=
          (PowerSeries.exp_pow_eq_rescale_exp _).symm

theorem actualAuxiliaryAtExp_jetVector_sum (P : ActualIntervals M) (h : Fin M)
    (hM : 0 < M) :
    (∑ j : Fin M,
      actualAuxiliaryAtExp P h j * auxiliaryJetVector M P.n j) =
      PowerSeries.exp ℚ ^ P.n * P.exponentialLocalJetCombination h.val := by
  classical
  let finOfNat : ℕ → Fin M := fun j => ⟨j % M, Nat.mod_lt _ hM⟩
  let g : ℕ → PowerSeries ℚ := fun j =>
    actualAuxiliaryAtExp P h (finOfNat j) * auxiliaryJetVector M P.n (finOfNat j)
  have huniv :
      (∑ j : Fin M,
        actualAuxiliaryAtExp P h j * auxiliaryJetVector M P.n j) =
        ∑ j : Fin M, g j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [g, finOfNat, Nat.mod_eq_of_lt j.isLt]
  rw [huniv, Fin.sum_univ_eq_sum_range g]
  have hclean :
      (∑ j ∈ Finset.range M, g j) =
        ∑ j ∈ Finset.range M,
          (∑ ell ∈ Finset.range (P.n + 1),
            PowerSeries.C (auxiliaryScale M P.n j *
              P.localCoefficient ell h.val j) * PowerSeries.exp ℚ ^ (P.n - ell)) *
            (PowerSeries.C (auxiliaryCommonScale M P.n)⁻¹ * PowerSeries.X ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < M := Finset.mem_range.mp hj
    have hjval : (finOfNat j).val = j := by
      dsimp [finOfNat]
      exact Nat.mod_eq_of_lt hjlt
    simp only [g, actualAuxiliaryAtExp_eq_sum, auxiliaryJetVector]
    rw [hjval]
  rw [hclean]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold ActualIntervals.exponentialLocalJetCombination
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have helln : ell ≤ P.n := by
    have := Finset.mem_range.mp hell
    omega
  have hratio : auxiliaryScale M P.n j *
      (auxiliaryCommonScale M P.n)⁻¹ =
        (Nat.factorial j : ℚ)⁻¹ :=
    auxiliaryScale_mul_commonScale_inv M P.n j
  have hconst :
      PowerSeries.C (auxiliaryScale M P.n j * P.localCoefficient ell h.val j) *
          PowerSeries.C (auxiliaryCommonScale M P.n)⁻¹ =
        PowerSeries.C (P.localCoefficient ell h.val j /
          (Nat.factorial j : ℚ)) := by
    rw [← map_mul]
    congr 1
    calc
      auxiliaryScale M P.n j * P.localCoefficient ell h.val j *
          (auxiliaryCommonScale M P.n)⁻¹ =
        P.localCoefficient ell h.val j *
          (auxiliaryScale M P.n j * (auxiliaryCommonScale M P.n)⁻¹) := by ring
      _ = P.localCoefficient ell h.val j * (Nat.factorial j : ℚ)⁻¹ := by
        rw [hratio]
      _ = P.localCoefficient ell h.val j / (Nat.factorial j : ℚ) := by
        rw [div_eq_mul_inv]
  calc
    _ = PowerSeries.exp ℚ ^ P.n *
        (PowerSeries.C (auxiliaryScale M P.n j * P.localCoefficient ell h.val j) *
          PowerSeries.C (auxiliaryCommonScale M P.n)⁻¹ * PowerSeries.X ^ j *
          PowerSeries.rescale (-(ell : ℚ)) (PowerSeries.exp ℚ)) := by
          rw [← exp_pow_mul_rescale_neg P.n ell helln]
          ring
    _ = _ := by rw [hconst]

theorem actualAuxiliaryExpMatrix_mulVec_jetVector_dvd
    (P : ActualIntervals M) (h : Fin M) (hM : 0 < M) :
    (PowerSeries.X : PowerSeries ℚ) ^ (∑ a : Fin M, P.length a) ∣
      Matrix.mulVec (actualAuxiliaryExpMatrix P)
        (auxiliaryJetVector M P.n) h := by
  classical
  let N := ∑ a : Fin M, P.length a
  have htotal := P.totalMultiplicity_eq_card_add_sum_length
  have horder : N + 1 ≤ P.totalMultiplicity - h.val := by
    rw [htotal]
    dsimp [N]
    omega
  have hjet := P.exponentialLocalJetCombination_dvd h hM N horder
  change (PowerSeries.X : PowerSeries ℚ) ^ N ∣
    ∑ j : Fin M, actualAuxiliaryAtExp P h j * auxiliaryJetVector M P.n j
  rw [actualAuxiliaryAtExp_jetVector_sum P h hM]
  rcases hjet with ⟨q, hq⟩
  refine ⟨PowerSeries.exp ℚ ^ P.n * q, ?_⟩
  calc
    PowerSeries.exp ℚ ^ P.n * P.exponentialLocalJetCombination h.val =
        PowerSeries.exp ℚ ^ P.n *
          ((PowerSeries.X : PowerSeries ℚ) ^ N * q) := by rw [hq]
    _ = (PowerSeries.X : PowerSeries ℚ) ^ N *
          (PowerSeries.exp ℚ ^ P.n * q) := by ring

/-- A column transformation whose first column is the exponential jet vector
and whose remaining columns are scaled coordinate vectors. -/
noncomputable def auxiliaryColumnTransform (P : ActualIntervals M) (N : ℕ) :
    Matrix (Fin M) (Fin M) (PowerSeries ℚ) :=
  fun i j =>
    if j.val = 0 then auxiliaryJetVector M P.n i
    else if i = j then (PowerSeries.X : PowerSeries ℚ) ^ N else 0

theorem auxiliaryColumnTransform_lower (P : ActualIntervals M) (N : ℕ) :
    (auxiliaryColumnTransform P N).IsLowerTriangular := by
  intro i j hij
  by_cases hj0 : j.val = 0
  · have : i.val < 0 := by simpa [Fin.lt_iff_val_lt_val, hj0] using hij
    omega
  · have hne : i ≠ j := by
      intro heq
      subst j
      exact (lt_irrefl (OrderDual.toDual i)) hij
    simp [auxiliaryColumnTransform, hj0, hne]

theorem auxiliaryColumnTransform_det (P : ActualIntervals M) (N : ℕ)
    (hM : 0 < M) :
    (auxiliaryColumnTransform P N).det =
      PowerSeries.C (auxiliaryCommonScale M P.n)⁻¹ *
        (PowerSeries.X : PowerSeries ℚ) ^ (N * (M - 1)) := by
  classical
  let z : Fin M := ⟨0, hM⟩
  let d : Fin M → PowerSeries ℚ := fun i =>
    if i.val = 0 then PowerSeries.C (auxiliaryCommonScale M P.n)⁻¹
    else (PowerSeries.X : PowerSeries ℚ) ^ N
  have hz : z ∈ (Finset.univ : Finset (Fin M)) := Finset.mem_univ _
  have hsplit := Finset.mul_prod_erase (Finset.univ : Finset (Fin M)) d hz
  have hprodErase :
      ∏ i ∈ (Finset.univ : Finset (Fin M)).erase z, d i =
        ((PowerSeries.X : PowerSeries ℚ) ^ N) ^ (M - 1) := by
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin M)).erase z,
        d i = (PowerSeries.X : PowerSeries ℚ) ^ N := by
      intro i hi
      have hne : i ≠ z := (Finset.mem_erase.mp hi).1
      have hi0 : i.val ≠ 0 := by
        intro hi0
        apply hne
        apply Fin.ext
        simpa [z] using hi0
      simp [d, hi0]
    have hcard : ((Finset.univ : Finset (Fin M)).erase z).card = M - 1 := by
      simp [Finset.card_erase_of_mem, hz]
    calc
      _ = ∏ i ∈ (Finset.univ : Finset (Fin M)).erase z,
          (PowerSeries.X : PowerSeries ℚ) ^ N := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hterm i hi
      _ = _ := by simp [hcard]
  calc
    (auxiliaryColumnTransform P N).det =
        ∏ i : Fin M, (auxiliaryColumnTransform P N) i i :=
          Matrix.det_of_isLowerTriangular _ (auxiliaryColumnTransform_lower P N)
    _ = ∏ i : Fin M, d i := by
          apply Finset.prod_congr rfl
          intro i hi
          by_cases hi0 : i.val = 0
          · simp [auxiliaryColumnTransform, auxiliaryJetVector, d, hi0]
          · simp [auxiliaryColumnTransform, auxiliaryJetVector, d, hi0]
    _ = d z * ∏ i ∈ (Finset.univ : Finset (Fin M)).erase z, d i := by
          simpa using hsplit.symm
    _ = PowerSeries.C (auxiliaryCommonScale M P.n)⁻¹ *
        (PowerSeries.X : PowerSeries ℚ) ^ (N * (M - 1)) := by
          rw [hprodErase]
          simp [d, z, pow_mul]

theorem auxiliaryColumnTransform_product_entry_dvd
    (P : ActualIntervals M) (N : ℕ) (h : Fin M) (j : Fin M)
    (hM : 0 < M) (hN : N = ∑ a : Fin M, P.length a) :
    (PowerSeries.X : PowerSeries ℚ) ^ N ∣
      (actualAuxiliaryExpMatrix P * auxiliaryColumnTransform P N) h j := by
  classical
  by_cases hj0 : j.val = 0
  · have hjz : j = ⟨0, hM⟩ := Fin.ext hj0
    subst j
    change (PowerSeries.X : PowerSeries ℚ) ^ N ∣
      ∑ k : Fin M,
        actualAuxiliaryExpMatrix P h k *
          auxiliaryColumnTransform P N k ⟨0, hM⟩
    have hrow := actualAuxiliaryExpMatrix_mulVec_jetVector_dvd P h hM
    rw [← hN] at hrow
    simpa [auxiliaryColumnTransform, Matrix.mulVec, dotProduct] using hrow
  · rw [Matrix.mul_apply]
    simp [auxiliaryColumnTransform, hj0]

theorem actualAuxiliaryExpMatrix_det_dvd (P : ActualIntervals M)
    (hM : 0 < M) :
    (PowerSeries.X : PowerSeries ℚ) ^ (∑ a : Fin M, P.length a) ∣
      (actualAuxiliaryExpMatrix P).det := by
  classical
  let N : ℕ := ∑ a : Fin M, P.length a
  let B : Matrix (Fin M) (Fin M) (PowerSeries ℚ) := actualAuxiliaryExpMatrix P
  let T : Matrix (Fin M) (Fin M) (PowerSeries ℚ) := auxiliaryColumnTransform P N
  let U : PowerSeries ℚ := PowerSeries.C (auxiliaryCommonScale M P.n)⁻¹
  let L : ℕ := N * (M - 1)
  let Q : Matrix (Fin M) (Fin M) (PowerSeries ℚ) := fun i j =>
    Classical.choose (auxiliaryColumnTransform_product_entry_dvd P N i j hM rfl)
  have hentry : ∀ i j, (B * T) i j =
      (PowerSeries.X : PowerSeries ℚ) ^ N * Q i j := by
    intro i j
    exact Classical.choose_spec
      (auxiliaryColumnTransform_product_entry_dvd P N i j hM rfl)
  have hmatrix : B * T = (PowerSeries.X : PowerSeries ℚ) ^ N • Q := by
    ext i j n
    simpa only [Matrix.smul_apply, smul_eq_mul] using
      congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff n f) (hentry i j)
  have hdet : B.det * T.det =
      (PowerSeries.X : PowerSeries ℚ) ^ (N * M) * Q.det := by
    calc
      B.det * T.det = (B * T).det := (Matrix.det_mul B T).symm
      _ = ((PowerSeries.X : PowerSeries ℚ) ^ N • Q).det := by rw [hmatrix]
      _ = _ := by rw [Matrix.det_smul]; simp [pow_mul]
  have hTdet : T.det = U * (PowerSeries.X : PowerSeries ℚ) ^ L := by
    simpa [T, U, L, N] using auxiliaryColumnTransform_det P N hM
  have hshiftDiv :
      (PowerSeries.X : PowerSeries ℚ) ^ (N * M) ∣
        (U * B.det) * (PowerSeries.X : PowerSeries ℚ) ^ L := by
    refine ⟨Q.det, ?_⟩
    calc
      (U * B.det) * (PowerSeries.X : PowerSeries ℚ) ^ L = B.det * T.det := by
        rw [hTdet]
        ring
      _ = (PowerSeries.X : PowerSeries ℚ) ^ (N * M) * Q.det := hdet
  rw [PowerSeries.X_pow_dvd_iff] at hshiftDiv
  have hdecomp : N * M = L + N := by
    have hMsub : (M - 1) + 1 = M := Nat.sub_add_cancel (by omega)
    dsimp [L]
    calc
      N * M = N * ((M - 1) + 1) :=
        congrArg (fun m : ℕ => N * m) hMsub.symm
      _ = N * (M - 1) + N := by rw [Nat.mul_add]; simp
  have hcoeff : ∀ k < N, PowerSeries.coeff k (U * B.det) = 0 := by
    intro k hk
    have hbound : k + L < N * M := by rw [hdecomp]; omega
    have hcoeff := hshiftDiv (k + L) hbound
    rw [PowerSeries.coeff_mul_X_pow] at hcoeff
    exact hcoeff
  have hU0 : PowerSeries.coeff 0 U ≠ 0 := by
    dsimp [U]
    simp [auxiliaryCommonScale_ne_zero]
  have hjet := (unit_mul_jets_iff U B.det N hU0).mp hcoeff
  have hBdiv : (PowerSeries.X : PowerSeries ℚ) ^ N ∣ B.det :=
    PowerSeries.X_pow_dvd_iff.mpr hjet
  simpa [B, N] using hBdiv

noncomputable def actualAuxiliaryPolynomialMatrix (P : ActualIntervals M) :
    Matrix (Fin M) (Fin M) (Polynomial ℚ) :=
  fun h j => actualAuxiliary P h j

noncomputable def actualAuxiliaryExponentialEval :
    Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.exp ℚ)

theorem actualAuxiliaryExpMatrix_eq_map (P : ActualIntervals M) :
    actualAuxiliaryExpMatrix P =
      RingHom.mapMatrix actualAuxiliaryExponentialEval
        (actualAuxiliaryPolynomialMatrix P) := by
  ext h j
  simp [actualAuxiliaryExpMatrix, actualAuxiliaryAtExp,
    actualAuxiliaryPolynomialMatrix, actualAuxiliaryExponentialEval]

theorem actualAuxiliaryPolynomialDet_exp_dvd (P : ActualIntervals M)
    (hM : 0 < M) :
    (PowerSeries.X : PowerSeries ℚ) ^ (∑ a : Fin M, P.length a) ∣
      actualAuxiliaryExponentialEval (actualAuxiliaryPolynomialMatrix P).det := by
  have h := actualAuxiliaryExpMatrix_det_dvd P hM
  rw [actualAuxiliaryExpMatrix_eq_map] at h
  simpa only [actualAuxiliaryExponentialEval, RingHom.map_det] using h

theorem actualAuxiliary_substLog_expEval_eq_shiftEval :
    (PowerSeries.substAlgHom PowerSeries.HasSubst.log).toRingHom.comp
      actualAuxiliaryExponentialEval =
        Polynomial.eval₂RingHom PowerSeries.C (1 + PowerSeries.X : PowerSeries ℚ) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    have hleft : actualAuxiliaryExponentialEval (Polynomial.C a) =
        PowerSeries.C a := by
      simpa [actualAuxiliaryExponentialEval] using
        congrFun (Polynomial.eval₂RingHom_comp_C PowerSeries.C
          (PowerSeries.exp ℚ)) a
    have hright :
        (Polynomial.eval₂RingHom PowerSeries.C
          (1 + PowerSeries.X : PowerSeries ℚ)) (Polynomial.C a) =
          PowerSeries.C a := by simp
    rw [hleft, hright]
    simpa [PowerSeries.C_eq_algebraMap] using
      (PowerSeries.substAlgHom PowerSeries.HasSubst.log).commutes a
  · simp only [RingHom.comp_apply]
    have hleft : actualAuxiliaryExponentialEval (Polynomial.X) =
        PowerSeries.exp ℚ := by
      simp [actualAuxiliaryExponentialEval]
    have hright :
        (Polynomial.eval₂RingHom PowerSeries.C
          (1 + PowerSeries.X : PowerSeries ℚ)) Polynomial.X =
          1 + PowerSeries.X := by simp
    rw [hleft, hright]
    change (⇑(PowerSeries.substAlgHom PowerSeries.HasSubst.log))
      (PowerSeries.exp ℚ) = 1 + PowerSeries.X
    rw [PowerSeries.coe_substAlgHom]
    exact PowerSeries.subst_exp_log ℚ

theorem actualAuxiliary_shiftEval_eq_coe_taylor_one (p : Polynomial ℚ) :
    Polynomial.eval₂RingHom PowerSeries.C (1 + PowerSeries.X : PowerSeries ℚ) p =
      Polynomial.coeToPowerSeries.ringHom (p.taylor 1) := by
  rw [Polynomial.taylor_apply, Polynomial.coeToPowerSeries.ringHom_apply]
  rw [← Polynomial.eval₂_C_X_eq_coe
    (φ := p.comp (X + C (1 : ℚ)))]
  rw [Polynomial.eval₂_comp]
  simp [add_comm]

theorem actualAuxiliaryPolynomialDet_taylor_dvd (P : ActualIntervals M)
    (hM : 0 < M) :
    (PowerSeries.X : PowerSeries ℚ) ^ (∑ a : Fin M, P.length a) ∣
      Polynomial.coeToPowerSeries.ringHom
        ((actualAuxiliaryPolynomialMatrix P).det.taylor 1) := by
  let N := ∑ a : Fin M, P.length a
  have hexp := actualAuxiliaryPolynomialDet_exp_dvd P hM
  change (PowerSeries.X : PowerSeries ℚ) ^ N ∣
    actualAuxiliaryExponentialEval (actualAuxiliaryPolynomialMatrix P).det at hexp
  have hXlog : (PowerSeries.X : PowerSeries ℚ) ∣ PowerSeries.log ℚ := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have hlogpow : (PowerSeries.X : PowerSeries ℚ) ^ N ∣
      (PowerSeries.log ℚ) ^ N := by
    rcases hXlog with ⟨q, hq⟩
    refine ⟨q ^ N, ?_⟩
    rw [hq, mul_pow]
  have hsubst : (PowerSeries.log ℚ) ^ N ∣
      (PowerSeries.substAlgHom PowerSeries.HasSubst.log).toRingHom
        (actualAuxiliaryExponentialEval (actualAuxiliaryPolynomialMatrix P).det) := by
    rcases hexp with ⟨q, hq⟩
    refine ⟨PowerSeries.substAlgHom PowerSeries.HasSubst.log q, ?_⟩
    rw [hq, map_mul, map_pow]
    change (PowerSeries.substAlgHom PowerSeries.HasSubst.log
        (PowerSeries.X : PowerSeries ℚ)) ^ N *
        (PowerSeries.substAlgHom PowerSeries.HasSubst.log q) = _
    rw [PowerSeries.substAlgHom_X]
  have heq := congrArg (fun f : Polynomial ℚ →+* PowerSeries ℚ =>
    f (actualAuxiliaryPolynomialMatrix P).det)
    actualAuxiliary_substLog_expEval_eq_shiftEval
  have heq' : (PowerSeries.substAlgHom PowerSeries.HasSubst.log).toRingHom
      (actualAuxiliaryExponentialEval (actualAuxiliaryPolynomialMatrix P).det) =
        Polynomial.eval₂RingHom PowerSeries.C (1 + PowerSeries.X : PowerSeries ℚ)
          (actualAuxiliaryPolynomialMatrix P).det := by
    simpa only [RingHom.comp_apply] using heq
  rw [actualAuxiliary_shiftEval_eq_coe_taylor_one] at heq'
  rw [heq'] at hsubst
  have hshift : (PowerSeries.X : PowerSeries ℚ) ^ N ∣
      Polynomial.coeToPowerSeries.ringHom
        ((actualAuxiliaryPolynomialMatrix P).det.taylor 1) :=
    dvd_trans hlogpow hsubst
  simpa [N] using hshift

theorem actualAuxiliaryPolynomialDet_X_sub_one_dvd (P : ActualIntervals M)
    (hM : 0 < M) :
    (X - 1 : Polynomial ℚ) ^ (∑ a : Fin M, P.length a) ∣
      (actualAuxiliaryPolynomialMatrix P).det := by
  have h := actualAuxiliaryPolynomialDet_taylor_dvd P hM
  have hcoeff : ∀ j < ∑ a : Fin M, P.length a,
      ((actualAuxiliaryPolynomialMatrix P).det.taylor 1).coeff j = 0 := by
    intro j hj
    have hj' := (PowerSeries.X_pow_dvd_iff.mp h) j hj
    simpa using hj'
  simpa using (pow_X_sub_C_dvd_iff_taylor
    (actualAuxiliaryPolynomialMatrix P).det 1 _).2 hcoeff

theorem actualAuxiliary_localCoefficient_mem {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) (ell : ℕ) (hell : ell ≤ P.n) :
    auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val ∈ integerRationals := by
  let m := M - 1
  let jj := j.val
  have hjm : jj ≤ m := by omega
  have hmu_le : P.multiplicity ell ≤ M := by
    have hs : (Finset.univ.filter (fun a : Fin M => ell ∈ P.interval a)) ⊆
        Finset.univ := by
      intro a ha
      simp
    simpa [ActualIntervals.multiplicity] using Finset.card_le_card hs
  by_cases hjlt : jj < P.multiplicity ell
  · let u := P.multiplicity ell - 1 - jj
    have hu : u + (M - P.multiplicity ell) ≤ m - jj := by
      dsimp [u, m]
      omega
    have hcleared := (P.localExpansion_cleared ell h.val hell).coeff_with_budget
      u (m - jj) hu
    have hdvd : jj.factorial ∣ m.factorial := Nat.factorial_dvd_factorial hjm
    let q := m.factorial / jj.factorial
    have hfac : jj.factorial * q = m.factorial := Nat.mul_div_cancel' hdvd
    have hpow : (intervalLcm P.n : ℚ) ^ m =
        (intervalLcm P.n : ℚ) ^ jj * (intervalLcm P.n : ℚ) ^ (m - jj) := by
      rw [← pow_add, Nat.add_sub_of_le hjm]
    have hscale : auxiliaryScale M P.n jj =
        (q : ℚ) * (intervalLcm P.n : ℚ) ^ jj *
          (intervalLcm P.n : ℚ) ^ (m - jj) := by
      unfold auxiliaryScale
      have hfacQ : (m.factorial : ℚ) = (jj.factorial : ℚ) * (q : ℚ) := by
        exact_mod_cast hfac.symm
      rw [hfacQ, hpow]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero jj)]
    have hq : (q : ℚ) ∈ integerRationals := intCast_mem_integerRationals q
    have hdj : (intervalLcm P.n : ℚ) ^ jj ∈ integerRationals := by
      have hd := intCast_mem_integerRationals ((intervalLcm P.n : ℤ) ^ jj)
      simpa using hd
    have hprod := integerRationals.mul_mem hq
      (integerRationals.mul_mem hdj hcleared)
    rw [show P.localCoefficient ell h.val jj =
        PowerSeries.coeff u (P.localExpansion ell h.val) by
          simp [ActualIntervals.localCoefficient, hjlt, u]]
    rw [show auxiliaryScale M P.n jj =
        (q : ℚ) * (intervalLcm P.n : ℚ) ^ jj *
          (intervalLcm P.n : ℚ) ^ (m - jj) from hscale]
    simpa [mul_assoc] using hprod
  · simp [ActualIntervals.localCoefficient, jj, hjlt]

def IntegerRationalPolynomial (p : Polynomial ℚ) : Prop :=
  ∀ k, p.coeff k ∈ integerRationals

theorem actualAuxiliary_integerRationalPolynomial {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) :
    IntegerRationalPolynomial (actualAuxiliary P h j) := by
  classical
  intro k
  rw [actualAuxiliary, Polynomial.finsetSum_coeff]
  apply integerRationals.sum_mem
  intro ell hell
  have hellrange : ell < P.n + 1 := Finset.mem_range.mp hell
  have helln : ell ≤ P.n := by omega
  have hc := actualAuxiliary_localCoefficient_mem P h j ell helln
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with heq
  · simpa using hc
  · exact integerRationals.zero_mem

/-- Choose the integer represented by a rational in the image subring. -/
noncomputable def integerRationalPreimage (q : ℚ) (hq : q ∈ integerRationals) : ℤ :=
  Classical.choose (RingHom.mem_range.mp hq)

theorem integerRationalPreimage_spec (q : ℚ) (hq : q ∈ integerRationals) :
    (integerRationalPreimage q hq : ℚ) = q :=
  Classical.choose_spec (RingHom.mem_range.mp hq)

/-- Lift a rational polynomial with integer coefficients to a polynomial over
the integers. -/
noncomputable def integerPolynomialLift (p : Polynomial ℚ)
    (hp : IntegerRationalPolynomial p) : Polynomial ℤ := by
  classical
  exact ∑ k ∈ p.support,
    C (integerRationalPreimage (p.coeff k) (hp k)) * X ^ k

theorem map_integerPolynomialLift (p : Polynomial ℚ)
    (hp : IntegerRationalPolynomial p) :
    Polynomial.map (Int.castRingHom ℚ) (integerPolynomialLift p hp) = p := by
  classical
  ext k
  by_cases hk : p.coeff k = 0 <;>
    simp [integerPolynomialLift, Polynomial.finsetSum_coeff, hk,
      integerRationalPreimage_spec]

/-- The auxiliary family as an actual integer polynomial, together with its
canonical rational image. -/
noncomputable def actualAuxiliaryInt {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) : Polynomial ℤ :=
  integerPolynomialLift (actualAuxiliary P h j)
    (actualAuxiliary_integerRationalPolynomial P h j)

theorem map_actualAuxiliaryInt {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) :
    Polynomial.map (Int.castRingHom ℚ) (actualAuxiliaryInt P h j) =
      actualAuxiliary P h j :=
  map_integerPolynomialLift _ _

theorem actualAuxiliary_support_divisible {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) :
    X ^ (P.n - P.right j) ∣ actualAuxiliary P h j := by
  classical
  rw [actualAuxiliary]
  apply Finset.dvd_sum
  intro ell hell
  have hnonmem_zero : ell ∉ P.interval j → P.localCoefficient ell h.val j.val = 0 := by
    intro hmem
    have hnot : ¬ j.val < P.multiplicity ell := by
      intro hjlt
      apply hmem
      apply (P.multiplicity_support_iff j ell).mp
      omega
    simp [ActualIntervals.localCoefficient, hnot]
  by_cases hmem : ell ∈ P.interval j
  · have hellright : ell ≤ P.right j := (P.interval_mem_iff j ell).mp hmem |>.2
    have hexp : P.n - P.right j ≤ P.n - ell := Nat.sub_le_sub_left hellright P.n
    let e := P.n - ell
    let k := P.n - P.right j
    refine ⟨C (auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val) *
      X ^ (e - k), ?_⟩
    have hexp' : e - k + k = e := Nat.sub_add_cancel hexp
    calc
      C (auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val) * X ^ e =
          C (auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val) *
            X ^ (e - k + k) := by rw [hexp']
      _ = X ^ k *
          (C (auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val) *
            X ^ (e - k)) := by rw [pow_add]; ring
  · simp [hnonmem_zero hmem]

theorem actualAuxiliary_natDegree_le {M : ℕ}
    (P : ActualIntervals M) (h j : Fin M) :
    (actualAuxiliary P h j).natDegree ≤ P.n - P.left j := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  classical
  rw [actualAuxiliary, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro ell hell
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with heq
  · by_cases hmem : ell ∈ P.interval j
    · have hleft := (P.interval_mem_iff j ell).mp hmem |>.1
      have hellrange := Finset.mem_range.mp hell
      omega
    · have hnot : ¬ j.val < P.multiplicity ell := by
        intro hjlt
        apply hmem
        apply (P.multiplicity_support_iff j ell).mp
        omega
      simp [ActualIntervals.localCoefficient, hnot]
  · simp

/-- The coefficient at the top of the allowed support column is the local
coefficient at its left endpoint. -/
theorem actualAuxiliary_topCoeff (P : ActualIntervals M) (h j : Fin M) :
    (actualAuxiliary P h j).coeff (P.n - P.left j) =
      auxiliaryScale M P.n j.val *
        P.localCoefficient (P.left j) h.val j.val := by
  classical
  have hleftmem : P.left j ∈ P.interval j := by
    apply (P.interval_mem_iff j (P.left j)).mpr
    exact ⟨le_rfl, P.left_le_right j⟩
  have hmu : j.val < P.multiplicity (P.left j) := by
    have h := (P.multiplicity_support_iff j (P.left j)).2 hleftmem
    exact Nat.lt_of_succ_le h
  have hleftn : P.left j ≤ P.n := by
    have h := P.left_bound j
    omega
  rw [actualAuxiliary, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem (P.left j)
    (Finset.mem_range.mpr (by omega : P.left j < P.n + 1))]
  · rw [Polynomial.coeff_C_mul_X_pow]
    simp [ActualIntervals.localCoefficient, hmu]
  · intro ell hell hne
    have helln : ell ≤ P.n := by
      have := Finset.mem_range.mp hell
      omega
    have hpow : P.n - ell ≠ P.n - P.left j := by
      intro heq
      have heq' : ell = P.left j := by omega
      exact hne heq'
    have hpow' : P.n - P.left j ≠ P.n - ell := Ne.symm hpow
    rw [Polynomial.coeff_C_mul]
    simp [hpow']

/-- The leading coefficient columns are precisely the designated local jets,
up to their explicit scalar normalization. -/
theorem actualAuxiliary_topCoeff_eq_localJet (P : ActualIntervals M)
    (h j : Fin M) :
    (actualAuxiliary P h j).coeff (P.n - P.left j) =
      auxiliaryScale M P.n j.val *
        PowerSeries.coeff (P.multiplicity (P.left j) - 1 - j.val)
          (P.localExpansion (P.left j) h.val) := by
  rw [actualAuxiliary_topCoeff P h j]
  have hleftmem : P.left j ∈ P.interval j := by
    apply (P.interval_mem_iff j (P.left j)).mpr
    exact ⟨le_rfl, P.left_le_right j⟩
  have hmu : j.val < P.multiplicity (P.left j) := by
    have h := (P.multiplicity_support_iff j (P.left j)).2 hleftmem
    exact Nat.lt_of_succ_le h
  simp [ActualIntervals.localCoefficient, hmu]

noncomputable def actualAuxiliaryNormalized (P : ActualIntervals M)
    (h j : Fin M) : Polynomial ℚ := by
  classical
  have hdvd := actualAuxiliary_support_divisible P h j
  have heq : P.n - P.right j = P.left j := by
    have hn := P.left_bound j
    dsimp [ActualIntervals.right]
    omega
  rw [heq] at hdvd
  exact Classical.choose hdvd

theorem actualAuxiliary_eq_X_left_mul_normalized (P : ActualIntervals M)
    (h j : Fin M) :
    actualAuxiliary P h j = (X : Polynomial ℚ) ^ P.left j *
      actualAuxiliaryNormalized P h j := by
  classical
  have hdvd := actualAuxiliary_support_divisible P h j
  have heq : P.n - P.right j = P.left j := by
    have hn := P.left_bound j
    dsimp [ActualIntervals.right]
    omega
  rw [heq] at hdvd
  exact Classical.choose_spec hdvd

theorem actualAuxiliaryNormalized_natDegree_le (P : ActualIntervals M)
    (h j : Fin M) :
    (actualAuxiliaryNormalized P h j).natDegree ≤ P.length j := by
  classical
  have hfactor := actualAuxiliary_eq_X_left_mul_normalized P h j
  have hbound := actualAuxiliary_natDegree_le P h j
  by_cases hq : actualAuxiliaryNormalized P h j = 0
  · simp [hq]
  · have hpow : (X : Polynomial ℚ) ^ P.left j ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    have hdeg : (actualAuxiliary P h j).natDegree =
        P.left j + (actualAuxiliaryNormalized P h j).natDegree := by
      rw [hfactor, Polynomial.natDegree_mul hpow hq,
        Polynomial.natDegree_X_pow]
    rw [hdeg] at hbound
    dsimp [ActualIntervals.length]
    have hleft := P.left_bound j
    omega

noncomputable def actualAuxiliaryNormalizedMatrix (P : ActualIntervals M) :
    Matrix (Fin M) (Fin M) (Polynomial ℚ) :=
  fun h j => actualAuxiliaryNormalized P h j

theorem actualAuxiliaryPolynomialMatrix_eq_diagonal_mul_normalized
    (P : ActualIntervals M) :
    actualAuxiliaryPolynomialMatrix P =
      actualAuxiliaryNormalizedMatrix P *
        Matrix.diagonal (fun j : Fin M => (X : Polynomial ℚ) ^ P.left j) := by
  apply Matrix.ext
  intro h j
  calc
    actualAuxiliary P h j = (X : Polynomial ℚ) ^ P.left j *
        actualAuxiliaryNormalized P h j := actualAuxiliary_eq_X_left_mul_normalized P h j
    _ = actualAuxiliaryNormalized P h j * (X : Polynomial ℚ) ^ P.left j := mul_comm _ _
    _ = (actualAuxiliaryNormalizedMatrix P *
        Matrix.diagonal (fun k : Fin M => (X : Polynomial ℚ) ^ P.left k)) h j := by
      simp [Matrix.mul_apply, Matrix.diagonal_apply,
        actualAuxiliaryNormalizedMatrix]

theorem actualAuxiliaryPolynomialDet_factor (P : ActualIntervals M) :
    (actualAuxiliaryPolynomialMatrix P).det =
      (X : Polynomial ℚ) ^ (∑ j : Fin M, P.left j) *
        (actualAuxiliaryNormalizedMatrix P).det := by
  rw [actualAuxiliaryPolynomialMatrix_eq_diagonal_mul_normalized,
    Matrix.det_mul, Matrix.det_diagonal]
  simp [Finset.prod_pow_eq_pow_sum]
  ring

theorem actualAuxiliaryNormalized_topCoeff_eq_localJet (P : ActualIntervals M)
    (h j : Fin M) :
    (actualAuxiliaryNormalized P h j).coeff (P.length j) =
      auxiliaryScale M P.n j.val *
        PowerSeries.coeff (P.multiplicity (P.left j) - 1 - j.val)
          (P.localExpansion (P.left j) h.val) := by
  have htop := actualAuxiliary_topCoeff_eq_localJet P h j
  have hlen : P.length j + P.left j = P.n - P.left j := by
    dsimp [ActualIntervals.length]
    have hleft := P.left_bound j
    omega
  have hcoeff :
      (actualAuxiliary P h j).coeff (P.n - P.left j) =
        (actualAuxiliaryNormalized P h j).coeff (P.length j) := by
    rw [actualAuxiliary_eq_X_left_mul_normalized P h j, ← hlen,
      Polynomial.coeff_X_pow_mul]
  rw [← hcoeff, htop]

noncomputable def actualAuxiliaryLeadingMatrix (P : ActualIntervals M) :
    Matrix (Fin M) (Fin M) ℚ :=
  fun h j => (actualAuxiliaryNormalized P h j).coeff (P.length j)

private theorem coeff_prod_top_of_degree_bounds {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial ℚ) (d : ι → ℕ)
    (hbound : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) =
      ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        Polynomial.coeff_mul_add_eq_of_natDegree_le]
      · rw [ih]
        · simp [ha]
        · intro i hi
          exact hbound i (Finset.mem_insert_of_mem hi)
      · exact hbound a (Finset.mem_insert_self a s)
      · calc
          (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, (f i).natDegree :=
            Polynomial.natDegree_prod_le s f
          _ ≤ ∑ i ∈ s, d i :=
            Finset.sum_le_sum fun i hi => hbound i (Finset.mem_insert_of_mem hi)

def columnTopCoefficientMatrix {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (Polynomial ℚ)) (d : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) ℚ :=
  fun i j => (A i j).coeff (d j)

theorem coeff_det_top_of_columnBounds {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (Polynomial ℚ)) (d : Fin m → ℕ)
    (hbound : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.coeff (∑ j, d j) = (columnTopCoefficientMatrix A d).det := by
  classical
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul]
  congr 1
  apply coeff_prod_top_of_degree_bounds
  intro i hi
  exact hbound (σ i) i

theorem actualAuxiliaryNormalizedMatrix_det_natDegree_le (P : ActualIntervals M) :
    (actualAuxiliaryNormalizedMatrix P).det.natDegree ≤
      ∑ j : Fin M, P.length j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  calc
    (Equiv.Perm.sign σ • ∏ h : Fin M,
        actualAuxiliaryNormalizedMatrix P (σ h) h).natDegree ≤
        (∏ h : Fin M, actualAuxiliaryNormalizedMatrix P (σ h) h).natDegree :=
          Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ j : Fin M, P.length j := by
      calc
        _ ≤ ∑ j : Fin M,
            (actualAuxiliaryNormalizedMatrix P (σ j) j).natDegree := by
          simpa using Polynomial.natDegree_prod_le
            (Finset.univ : Finset (Fin M))
            (fun j => actualAuxiliaryNormalizedMatrix P (σ j) j)
        _ ≤ ∑ j : Fin M, P.length j :=
          Finset.sum_le_sum fun j hj => actualAuxiliaryNormalized_natDegree_le P (σ j) j

theorem actualAuxiliaryNormalizedMatrix_det_coeff_eq_leadingDet
    (P : ActualIntervals M) :
    (actualAuxiliaryNormalizedMatrix P).det.coeff (∑ j : Fin M, P.length j) =
      (actualAuxiliaryLeadingMatrix P).det := by
  have hcoeff := coeff_det_top_of_columnBounds (actualAuxiliaryNormalizedMatrix P)
    (fun j => P.length j)
    (by intro h j; exact actualAuxiliaryNormalized_natDegree_le P h j)
  have hmatrix :
      columnTopCoefficientMatrix (actualAuxiliaryNormalizedMatrix P)
          (fun j => P.length j) = actualAuxiliaryLeadingMatrix P := by
    ext h j
    rfl
  rw [hmatrix] at hcoeff
  exact hcoeff

theorem natDegree_det_le_of_columnBounds {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (Polynomial ℚ)) (d : Fin m → ℕ)
    (hbound : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  calc
    (Equiv.Perm.sign σ • ∏ i : Fin m, A (σ i) i).natDegree ≤
        (∏ i : Fin m, A (σ i) i).natDegree := Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ i : Fin m, d i := by
      calc
        _ ≤ ∑ i : Fin m, (A (σ i) i).natDegree := by
          simpa using Polynomial.natDegree_prod_le
            (Finset.univ : Finset (Fin m)) (fun i => A (σ i) i)
        _ ≤ ∑ i : Fin m, d i :=
          Finset.sum_le_sum fun i hi => hbound (σ i) i

def actualAuxiliaryLeftNodes (P : ActualIntervals M) : Finset ℕ :=
  Finset.univ.image P.left

abbrev ActualAuxiliaryLeftNode (P : ActualIntervals M) :=
  {ell : ℕ // ell ∈ actualAuxiliaryLeftNodes P}

def actualAuxiliaryLeftBlockSize (P : ActualIntervals M)
    (ell : ActualAuxiliaryLeftNode P) : ℕ :=
  (Finset.univ.filter fun j : Fin M => P.left j = ell.val).card

theorem actualAuxiliaryLeftBlockSize_sum (P : ActualIntervals M) :
    ∑ ell : ActualAuxiliaryLeftNode P, actualAuxiliaryLeftBlockSize P ell = M := by
  classical
  change ∑ ell : {ell : ℕ // ell ∈ actualAuxiliaryLeftNodes P},
    (Finset.univ.filter fun j : Fin M => P.left j = ell.val).card = M
  rw [← Finset.sum_subtype (s := actualAuxiliaryLeftNodes P)
    (h := fun _ => Iff.rfl)
    (f := fun ell => (Finset.univ.filter fun j : Fin M => P.left j = ell).card)]
  simpa [actualAuxiliaryLeftNodes, actualAuxiliaryLeftBlockSize] using
    (Finset.card_eq_sum_card_image P.left (Finset.univ : Finset (Fin M))).symm

private theorem ofFn_taylor_eq_sum (v : Fin M → ℚ) (ell : ℕ) :
    (Polynomial.ofFn M v).taylor (-(ell : ℚ)) =
      ∑ h : Fin M, Polynomial.C (v h) *
        (Polynomial.X + Polynomial.C (-(ell : ℚ))) ^ h.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [map_sum, Polynomial.taylor_monomial]

/-- The sum of a column's local coefficients against a vector is exactly the
corresponding coefficient of the common unit times the Taylor expansion. -/
theorem localExpansion_coeff_sum_eq_unit_taylor (P : ActualIntervals M)
    (v : Fin M → ℚ) (ell q : ℕ) :
    (∑ h : Fin M, v h * PowerSeries.coeff q (P.localExpansion ell h.val)) =
      PowerSeries.coeff q
        (P.localUnit ell *
          (Polynomial.coeToPowerSeries.ringHom
            ((Polynomial.ofFn M v).taylor (-(ell : ℚ))))) := by
  classical
  have hpoly := congrArg Polynomial.coeToPowerSeries.ringHom
    (ofFn_taylor_eq_sum (M := M) v ell)
  have hseries :
      Polynomial.coeToPowerSeries.ringHom
        ((Polynomial.ofFn M v).taylor (-(ell : ℚ))) =
        ∑ h : Fin M, PowerSeries.C (v h) *
          (PowerSeries.C (-(ell : ℚ)) + PowerSeries.X) ^ h.val := by
    calc
      _ = ∑ h : Fin M, PowerSeries.C (v h) *
          (PowerSeries.X + PowerSeries.C (-(ell : ℚ))) ^ h.val := by
            simpa only [map_sum, map_mul, map_pow, map_add,
              Polynomial.coeToPowerSeries.ringHom_apply,
              Polynomial.coe_C, Polynomial.coe_X] using hpoly
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [add_comm]
  have hprod : P.localUnit ell *
      Polynomial.coeToPowerSeries.ringHom
        ((Polynomial.ofFn M v).taylor (-(ell : ℚ))) =
      ∑ h : Fin M, PowerSeries.C (v h) * P.localExpansion ell h.val := by
    rw [hseries, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    simp only [ActualIntervals.localExpansion, ActualIntervals.localUnit]
    ring
  have hcoeff := congrArg (PowerSeries.coeff q) hprod
  rw [map_sum] at hcoeff
  simp_rw [PowerSeries.coeff_C_mul] at hcoeff
  simpa [mul_comm] using hcoeff.symm

theorem actualAuxiliaryLeftBlock_jet_orders (P : ActualIntervals M)
    (ell : ActualAuxiliaryLeftNode P) (q : ℕ)
    (hq : q < actualAuxiliaryLeftBlockSize P ell) :
    ∃ j : Fin M, P.left j = ell.val ∧
      q = P.multiplicity ell.val - 1 - j.val := by
  classical
  let F : Finset (Fin M) :=
    Finset.univ.filter fun j => P.left j = ell.val
  let low : Finset (Fin M) :=
    Finset.univ.filter fun j => P.left j < ell.val
  let le : Finset (Fin M) :=
    Finset.univ.filter fun j => P.left j ≤ ell.val
  let order (j : Fin M) : ℕ := P.multiplicity ell.val - 1 - j.val
  have hnode : 2 * ell.val ≤ P.n := by
    rcases Finset.mem_image.mp ell.property with ⟨a, ha, hleft⟩
    have := P.left_bound a
    simpa [hleft] using this
  have hle_card : P.multiplicity ell.val = le.card := by
    change (Finset.univ.filter
        (fun j : Fin M => ell.val ∈ P.interval j)).card = le.card
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, le]
    change (ell.val ∈ P.interval j) ↔ P.left j ≤ ell.val
    rw [P.interval_mem_iff]
    constructor
    · exact fun h => h.1
    · intro hj
      exact ⟨hj, by change ell.val ≤ P.n - P.left j; omega⟩
  have hdecomp : le = low ∪ F := by
    ext j
    simp only [le, low, F, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    omega
  have hdisj : Disjoint low F := by
    rw [Finset.disjoint_left]
    intro j hjlow hjF
    simp only [low, F, Finset.mem_filter, Finset.mem_univ, true_and] at hjlow hjF
    omega
  have hsum : P.multiplicity ell.val = low.card + F.card := by
    rw [hle_card, hdecomp, Finset.card_union_of_disjoint hdisj]
  have hFcard : F.card = actualAuxiliaryLeftBlockSize P ell := by
    rfl
  have hmu_sum : P.multiplicity ell.val = low.card +
      actualAuxiliaryLeftBlockSize P ell := by
    rw [← hFcard]
    exact hsum
  have hmem_interval (j : Fin M) (hjF : j ∈ F) :
      ell.val ∈ P.interval j := by
    have hleft : P.left j = ell.val := by
      simpa [F] using (Finset.mem_filter.mp hjF).2
    apply (P.interval_mem_iff j ell.val).2
    constructor
    · omega
    · change ell.val ≤ P.n - P.left j
      omega
  have hmu_index (j : Fin M) (hjF : j ∈ F) :
      j.val + 1 ≤ P.multiplicity ell.val := by
    exact (P.multiplicity_support_iff j ell.val).2 (hmem_interval j hjF)
  have hlow_index (j : Fin M) (hjF : j ∈ F) : low.card ≤ j.val := by
    have hleftj : P.left j = ell.val := by
      simpa [F] using (Finset.mem_filter.mp hjF).2
    have hsubset : low ⊆ Finset.Iio j := by
      intro k hk
      have hklt : P.left k < ell.val := by
        simpa [low] using (Finset.mem_filter.mp hk).2
      apply Finset.mem_Iio.mpr
      by_contra hnot
      have hjk : j ≤ k := le_of_not_gt hnot
      have hmono := P.left_mono hjk
      omega
    have hcard := Finset.card_le_card hsubset
    simpa [Fin.card_Iio] using hcard
  have horder_lt (j : Fin M) (hjF : j ∈ F) : order j <
      actualAuxiliaryLeftBlockSize P ell := by
    have hmu := hmu_index j hjF
    have hlo := hlow_index j hjF
    dsimp [order]
    rw [hmu_sum]
    omega
  have hinj : Set.InjOn order F := by
    intro j hj k hk heq
    have hjmu := hmu_index j hj
    have hkmu := hmu_index k hk
    dsimp [order] at heq
    have hval : j.val = k.val := by omega
    exact Fin.ext hval
  have himage_subset : F.image order ⊆
      Finset.range (actualAuxiliaryLeftBlockSize P ell) := by
    intro q' hq'
    rcases Finset.mem_image.mp hq' with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (horder_lt j hj)
  have himage_card : (F.image order).card =
      actualAuxiliaryLeftBlockSize P ell := by
    calc
      (F.image order).card = F.card := Finset.card_image_of_injOn hinj
      _ = actualAuxiliaryLeftBlockSize P ell := hFcard
  have himage : F.image order =
      Finset.range (actualAuxiliaryLeftBlockSize P ell) :=
    Finset.eq_of_subset_of_card_le himage_subset (by
      rw [Finset.card_range, himage_card])
  have hqimage : q ∈ F.image order := by
    rw [himage]
    exact Finset.mem_range.mpr hq
  rcases Finset.mem_image.mp hqimage with ⟨j, hj, horder⟩
  exact ⟨j, (Finset.mem_filter.mp hj).2, horder.symm⟩

theorem actualAuxiliaryLeadingMatrix_det_ne_zero (P : ActualIntervals M) :
    (actualAuxiliaryLeadingMatrix P).det ≠ 0 := by
  classical
  by_cases hM : 0 < M
  · intro hdet
    have hdetT : (actualAuxiliaryLeadingMatrix P).transpose.det = 0 := by
      rw [Matrix.det_transpose, hdet]
    obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdetT
    let p : Polynomial ℚ := Polynomial.ofFn M v
    have hpdeg : p.natDegree <
        ∑ ell : ActualAuxiliaryLeftNode P, actualAuxiliaryLeftBlockSize P ell := by
      calc
        p.natDegree < M := by
          exact Polynomial.ofFn_natDegree_lt
            (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt hM)) v
        _ = ∑ ell : ActualAuxiliaryLeftNode P,
            actualAuxiliaryLeftBlockSize P ell :=
          (actualAuxiliaryLeftBlockSize_sum P).symm
    have hjets : ∀ ell : ActualAuxiliaryLeftNode P,
        ∀ q < actualAuxiliaryLeftBlockSize P ell,
          PowerSeries.coeff q
            (P.localUnit ell.val *
              Polynomial.coeToPowerSeries.ringHom
                (p.taylor (-(ell.val : ℚ)))) = 0 := by
      intro ell q hq
      obtain ⟨j, hleft, horder⟩ :=
        actualAuxiliaryLeftBlock_jet_orders P ell q hq
      have hjzero := congrFun hz j
      have hdot : (∑ h : Fin M,
          actualAuxiliaryLeadingMatrix P h j * v h) = 0 := by
        simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
          Pi.zero_apply] using hjzero
      have hmatrixJet : (∑ h : Fin M,
          (auxiliaryScale M P.n j.val *
            PowerSeries.coeff
              (P.multiplicity (P.left j) - 1 - j.val)
              (P.localExpansion (P.left j) h.val)) * v h) = 0 := by
        calc
          _ = ∑ h : Fin M, actualAuxiliaryLeadingMatrix P h j * v h := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [actualAuxiliaryLeadingMatrix,
              actualAuxiliaryNormalized_topCoeff_eq_localJet]
          _ = 0 := hdot
      have hscale : auxiliaryScale M P.n j.val ≠ 0 := by
        intro hzscale
        have hcommon := auxiliaryScale_mul_factorial M P.n j.val
        rw [hzscale] at hcommon
        have hfactorial : (Nat.factorial j.val : ℚ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero j.val
        simp only [zero_mul] at hcommon
        exact auxiliaryCommonScale_ne_zero M P.n hcommon.symm
      have hsumzero :
          auxiliaryScale M P.n j.val *
            (∑ h : Fin M, v h *
              PowerSeries.coeff q (P.localExpansion ell.val h.val)) = 0 := by
        calc
          _ = ∑ h : Fin M,
              (auxiliaryScale M P.n j.val *
                PowerSeries.coeff q (P.localExpansion ell.val h.val)) * v h := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro h hh
                  ring
          _ = 0 := by
            simpa [hleft, horder] using hmatrixJet
      have hsum : ∑ h : Fin M, v h *
          PowerSeries.coeff q (P.localExpansion ell.val h.val) = 0 :=
        (mul_eq_zero.mp hsumzero).resolve_left hscale
      rw [← localExpansion_coeff_sum_eq_unit_taylor P v ell.val q]
      exact hsum
    let a : ActualAuxiliaryLeftNode P → ℚ := fun ell => -(ell.val : ℚ)
    let r : ActualAuxiliaryLeftNode P → ℕ := actualAuxiliaryLeftBlockSize P
    let B : ActualAuxiliaryLeftNode P → PowerSeries ℚ :=
      fun ell => P.localUnit ell.val
    have hainj : Function.Injective a := by
      intro ell₁ ell₂ heq
      apply Subtype.ext
      exact_mod_cast (neg_injective heq)
    have hB : ∀ ell, PowerSeries.coeff 0 (B ell) ≠ 0 := by
      intro ell
      simpa only [B, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        P.localUnit_constantCoeff_ne_zero ell.val
    have hpzero : p = 0 :=
      eq_zero_of_unit_weighted_jets a hainj r B hB p hpdeg hjets
    apply hv
    apply Polynomial.injective_ofFn M
    simpa [p] using hpzero
  · have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
    subst M
    simp [actualAuxiliaryLeadingMatrix]

theorem actualAuxiliaryNormalizedMatrix_det_X_sub_one_dvd
    (P : ActualIntervals M) (hM : 0 < M) :
    (X - 1 : Polynomial ℚ) ^ (∑ j : Fin M, P.length j) ∣
      (actualAuxiliaryNormalizedMatrix P).det := by
  classical
  let N : ℕ := ∑ j : Fin M, P.length j
  let F : Polynomial ℚ := (actualAuxiliaryNormalizedMatrix P).det
  let G : Polynomial ℚ := (actualAuxiliaryPolynomialMatrix P).det
  let B : PowerSeries ℚ := Polynomial.coeToPowerSeries.ringHom
    (((X : Polynomial ℚ) ^ (∑ j : Fin M, P.left j)).taylor 1)
  let T : PowerSeries ℚ := Polynomial.coeToPowerSeries.ringHom (F.taylor 1)
  have hTaylor : Polynomial.coeToPowerSeries.ringHom (G.taylor 1) = B * T := by
    have hpoly : G.taylor 1 =
        ((X : Polynomial ℚ) ^ (∑ j : Fin M, P.left j)).taylor 1 * F.taylor 1 := by
      rw [show G = (X : Polynomial ℚ) ^ (∑ j : Fin M, P.left j) * F from
        actualAuxiliaryPolynomialDet_factor P, Polynomial.taylor_mul]
    simpa only [B, T, map_mul, Polynomial.coeToPowerSeries.ringHom_apply] using
      congrArg Polynomial.coeToPowerSeries.ringHom hpoly
  have hB0 : PowerSeries.coeff 0 B ≠ 0 := by
    simp [B, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.taylor_coeff_zero]
  have hGA : (PowerSeries.X : PowerSeries ℚ) ^ N ∣
      Polynomial.coeToPowerSeries.ringHom (G.taylor 1) := by
    simpa only [G, N] using actualAuxiliaryPolynomialDet_taylor_dvd P hM
  have hcoeffA : ∀ q < N,
      PowerSeries.coeff q (Polynomial.coeToPowerSeries.ringHom (G.taylor 1)) = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp hGA)
  have hcoeffProduct : ∀ q < N, PowerSeries.coeff q (B * T) = 0 := by
    simpa only [hTaylor] using hcoeffA
  have hcoeffT := (unit_mul_jets_iff B T N hB0).1 hcoeffProduct
  have hTaylorCoeffs : ∀ q < N, (F.taylor 1).coeff q = 0 := by
    intro q hq
    simpa only [T, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeff_coe] using hcoeffT q hq
  have hFdiv := (pow_X_sub_C_dvd_iff_taylor F 1 N).2 hTaylorCoeffs
  simpa [F, N] using hFdiv

theorem actualAuxiliaryNormalizedMatrix_det_factorization
    (P : ActualIntervals M) (hM : 0 < M) :
    (actualAuxiliaryNormalizedMatrix P).det =
      Polynomial.C ((actualAuxiliaryLeadingMatrix P).det) *
        (X - 1 : Polynomial ℚ) ^ (∑ j : Fin M, P.length j) := by
  classical
  let N : ℕ := ∑ j : Fin M, P.length j
  let F : Polynomial ℚ := (actualAuxiliaryNormalizedMatrix P).det
  obtain ⟨q, hq⟩ := actualAuxiliaryNormalizedMatrix_det_X_sub_one_dvd P hM
  change F = (X - 1 : Polynomial ℚ) ^ N * q at hq
  have htop : F.coeff N ≠ 0 := by
    change ((actualAuxiliaryNormalizedMatrix P).det).coeff N ≠ 0
    rw [actualAuxiliaryNormalizedMatrix_det_coeff_eq_leadingDet]
    exact actualAuxiliaryLeadingMatrix_det_ne_zero P
  have hFbound : F.natDegree ≤ N := by
    simpa only [F, N] using actualAuxiliaryNormalizedMatrix_det_natDegree_le P
  have hFdegree : F.natDegree = N :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hFbound htop
  have hqne : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hq
    rw [hq] at htop
    simp at htop
  have hfactorDegree : ((X - 1 : Polynomial ℚ) ^ N).natDegree = N := by
    change ((X - Polynomial.C (1 : ℚ)) ^ N).natDegree = N
    simpa only [Polynomial.natDegree_X_sub_C, mul_one] using
      (Polynomial.monic_X_sub_C (1 : ℚ)).natDegree_pow N
  have hfactorDegree' :
      ((X - Polynomial.C (1 : ℚ)) ^ N).natDegree = N := by
    simpa only [Polynomial.natDegree_X_sub_C, mul_one] using
      (Polynomial.monic_X_sub_C (1 : ℚ)).natDegree_pow N
  have hprodDegree : F.natDegree = N + q.natDegree := by
    calc
      F.natDegree = ((X - 1 : Polynomial ℚ) ^ N * q).natDegree := by rw [hq]
      _ = ((X - 1 : Polynomial ℚ) ^ N).natDegree + q.natDegree :=
        Polynomial.natDegree_mul
          (pow_ne_zero N (Polynomial.X_sub_C_ne_zero 1)) hqne
      _ = N + q.natDegree := by rw [hfactorDegree]
  have hqdegree : q.natDegree = 0 := by
    rw [hFdegree] at hprodDegree
    omega
  have hqconst : q = Polynomial.C (q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero (by omega)
  have hcoeffQuotient : F.coeff N = q.coeff 0 := by
    rw [hq, hqconst]
    have hcoefFactor : ((X - 1 : Polynomial ℚ) ^ N).coeff N = 1 := by
      have hcoefFactor' :
          ((X - Polynomial.C (1 : ℚ)) ^ N).coeff N = 1 := by
        simpa only [hfactorDegree'] using
          ((Polynomial.monic_X_sub_C (1 : ℚ)).pow N).coeff_natDegree
      simpa [Polynomial.C_1] using hcoefFactor'
    have hmul := Polynomial.coeff_mul_add_eq_of_natDegree_le
      (f := (X - 1 : Polynomial ℚ) ^ N)
      (g := Polynomial.C (q.coeff 0)) (df := N) (dg := 0)
      hfactorDegree.le
      (by simp)
    simpa [hcoefFactor] using hmul
  have hquotient_eq_leading : q.coeff 0 =
      (actualAuxiliaryLeadingMatrix P).det := by
    calc
      q.coeff 0 = F.coeff N := hcoeffQuotient.symm
      _ = (actualAuxiliaryLeadingMatrix P).det := by
        simpa only [F, N] using actualAuxiliaryNormalizedMatrix_det_coeff_eq_leadingDet P
  calc
    (actualAuxiliaryNormalizedMatrix P).det =
        (X - 1 : Polynomial ℚ) ^ N * q := hq
    _ = Polynomial.C ((actualAuxiliaryLeadingMatrix P).det) *
        (X - 1 : Polynomial ℚ) ^ N := by
      rw [hqconst, ← hquotient_eq_leading]
      ring
    _ = _ := by simp only [N]

theorem actualAuxiliaryPolynomialDet_factorization
    (P : ActualIntervals M) :
    (actualAuxiliaryPolynomialMatrix P).det =
      Polynomial.C ((actualAuxiliaryLeadingMatrix P).det) *
        (X : Polynomial ℚ) ^ (∑ j : Fin M, P.left j) *
          (X - 1 : Polynomial ℚ) ^ (∑ j : Fin M, P.length j) := by
  by_cases hM : 0 < M
  · rw [actualAuxiliaryPolynomialDet_factor P,
      actualAuxiliaryNormalizedMatrix_det_factorization P hM]
    ring
  · have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
    subst M
    simp [actualAuxiliaryPolynomialMatrix, actualAuxiliaryLeadingMatrix]

noncomputable def actualAuxiliaryPolynomialEvalI :
    Polynomial ℚ →+* ℂ := Polynomial.eval₂RingHom (Rat.castHom ℂ) Complex.I

noncomputable def actualAuxiliaryPolynomialMatrixAtI (P : ActualIntervals M) :
    Matrix (Fin M) (Fin M) ℂ :=
  RingHom.mapMatrix actualAuxiliaryPolynomialEvalI
    (actualAuxiliaryPolynomialMatrix P)

theorem actualAuxiliaryPolynomialMatrixAtI_det_eq (P : ActualIntervals M) :
    Matrix.det (actualAuxiliaryPolynomialMatrixAtI P :
      Matrix (Fin M) (Fin M) ℂ) =
      actualAuxiliaryPolynomialEvalI
        (actualAuxiliaryPolynomialMatrix P).det := by
  simp [actualAuxiliaryPolynomialMatrixAtI, RingHom.map_det]

theorem actualAuxiliaryPolynomialMatrixAtI_det_ne_zero
    (P : ActualIntervals M) :
    Matrix.det (actualAuxiliaryPolynomialMatrixAtI P :
      Matrix (Fin M) (Fin M) ℂ) ≠ (0 : ℂ) := by
  rw [actualAuxiliaryPolynomialMatrixAtI_det_eq,
    actualAuxiliaryPolynomialDet_factorization P]
  simp only [actualAuxiliaryPolynomialEvalI, Polynomial.coe_eval₂RingHom,
    map_mul, map_pow, map_sub, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_one]
  apply mul_ne_zero
  · apply mul_ne_zero
    · change ((actualAuxiliaryLeadingMatrix P).det : ℂ) ≠ 0
      exact_mod_cast actualAuxiliaryLeadingMatrix_det_ne_zero P
    · exact pow_ne_zero _ Complex.I_ne_zero
  · have hi1 : Complex.I - (1 : ℂ) ≠ 0 := by
      intro h
      have hIm := congrArg Complex.im h
      have hone : (1 : ℝ) = 0 := by simpa using hIm
      exact one_ne_zero hone
    exact pow_ne_zero _ hi1

end OddPiPowers
