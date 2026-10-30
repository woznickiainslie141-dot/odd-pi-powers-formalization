module

public import OddPiPowers.Analysis.PeriodGapTail
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs
public import Mathlib.Data.Rat.Cast.Order

/-! Small rational certificates for each finite tail, before summation. -/

@[expose] public section

namespace OddPiPowers.L99.PrimeRates

open OddPiPowers.PrimeRates

def rationalPeriodGap (r : ℕ) (a b : ℚ) : ℚ := 1 / (r + a) - 1 / (r + b)

def periodTailRational (T K : ℕ) (c : TwentyEightCellCertificate) : ℚ :=
  let x := (c.right - c.left) / (T + c.left)
  let y := (c.right - c.left) / (K + c.left)
  (c.value : ℚ) / 99 * (x - x ^ 2 / 2 - y +
    (rationalPeriodGap T c.left c.right - rationalPeriodGap K c.left c.right) / 2)

theorem periodTailRational_le (T K : ℕ) (hT : 1 ≤ T) (hTK : T ≤ K)
    (c : TwentyEightCellCertificate) (ha : (0 : ℝ) < (c.left : ℝ))
    (hab : (c.left : ℝ) < (c.right : ℝ)) :
    (periodTailRational T K c : ℝ) ≤ (c.value : ℝ) / 99 *
      ∑ r ∈ Finset.Ico T K, periodGap r (c.left : ℝ) (c.right : ℝ) := by
  have h := periodGap_finite_rational_lower (c.left : ℝ) (c.right : ℝ) ha hab T K hT hTK
  have hm := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (c.value : ℝ) / 99)
  convert hm using 1
  simp only [periodTailRational, rationalPeriodGap, periodGap]
  push_cast
  rfl

def periodTailDenominator (T K : ℕ) (c : TwentyEightCellCertificate) : ℕ :=
  let u := T * c.leftDenominator + c.leftNumerator
  let v := K * c.leftDenominator + c.leftNumerator
  let w := T * c.rightDenominator + c.rightNumerator
  let z := K * c.rightDenominator + c.rightNumerator
  99 * 2 * c.rightDenominator ^ 2 * u ^ 2 * v * w * z

def periodTailNumerator (T K : ℕ) (c : TwentyEightCellCertificate) : ℤ :=
  let d : ℤ := (c.rightNumerator * c.leftDenominator -
    c.leftNumerator * c.rightDenominator : ℕ)
  let D : ℤ := c.rightDenominator
  let u : ℤ := T * c.leftDenominator + c.leftNumerator
  let v : ℤ := K * c.leftDenominator + c.leftNumerator
  let w : ℤ := T * c.rightDenominator + c.rightNumerator
  let z : ℤ := K * c.rightDenominator + c.rightNumerator
  (c.value : ℤ) * (2 * d * D * u * v * w * z - d ^ 2 * v * w * z -
    2 * d * D * u ^ 2 * w * z + d * D ^ 2 * u * v * z - d * D ^ 2 * u ^ 2 * w)

theorem periodTail_eq_fraction (T K : ℕ) (c : TwentyEightCellCertificate)
    (hA : 0 < c.leftNumerator) (hC : 0 < c.leftDenominator)
    (hD : 0 < c.rightDenominator)
    (ho : c.leftNumerator * c.rightDenominator < c.rightNumerator * c.leftDenominator) :
    (periodTailRational T K c : ℝ) = (periodTailNumerator T K c : ℝ) /
      (periodTailDenominator T K c : ℝ) := by
  have hB : 0 < c.rightNumerator := by
    by_contra h
    have hz : c.rightNumerator = 0 := by omega
    simp [hz] at ho
  have hAr : (0 : ℝ) < c.leftNumerator := by exact_mod_cast hA
  have hCr : (0 : ℝ) < c.leftDenominator := by exact_mod_cast hC
  have hDr : (0 : ℝ) < c.rightDenominator := by exact_mod_cast hD
  have hBr : (0 : ℝ) < c.rightNumerator := by exact_mod_cast hB
  have hu : (0 : ℝ) < (T : ℝ) * c.leftDenominator + c.leftNumerator := by positivity
  have hv : (0 : ℝ) < (K : ℝ) * c.leftDenominator + c.leftNumerator := by positivity
  have hw : (0 : ℝ) < (T : ℝ) * c.rightDenominator + c.rightNumerator := by positivity
  have hz : (0 : ℝ) < (K : ℝ) * c.rightDenominator + c.rightNumerator := by positivity
  simp only [periodTailRational, rationalPeriodGap, TwentyEightCellCertificate.left,
    TwentyEightCellCertificate.right, periodTailNumerator, periodTailDenominator]
  push_cast
  rw [Nat.cast_sub ho.le]
  push_cast
  field_simp [hCr.ne', hDr.ne', hu.ne', hv.ne', hw.ne', hz.ne'] <;> ring

def tailFloorCheck (scale T K : ℕ) (c : TwentyEightCellCertificate) (q : ℕ) : Bool :=
  decide (0 < scale ∧ 0 < c.leftNumerator ∧ 0 < c.leftDenominator ∧
    0 < c.rightDenominator ∧
    c.leftNumerator * c.rightDenominator < c.rightNumerator * c.leftDenominator ∧
    (q : ℤ) * periodTailDenominator T K c ≤ (scale : ℤ) * periodTailNumerator T K c)

theorem tailFloorCheck_sound (scale T K : ℕ) (c : TwentyEightCellCertificate) (q : ℕ)
    (h : tailFloorCheck scale T K c q = true) :
    (q : ℝ) / scale ≤ (periodTailRational T K c : ℝ) := by
  have hh := of_decide_eq_true h
  have hB : 0 < c.rightNumerator := by
    by_contra hb
    have hz : c.rightNumerator = 0 := by omega
    simpa only [hz, Nat.zero_mul, Nat.not_lt_zero] using hh.2.2.2.2.1
  have hs : (0 : ℝ) < scale := by exact_mod_cast hh.1
  have hdN : 0 < periodTailDenominator T K c := by
    have hA := hh.2.1
    have hC := hh.2.2.1
    have hD := hh.2.2.2.1
    unfold periodTailDenominator
    positivity
  have hd : (0 : ℝ) < periodTailDenominator T K c := by exact_mod_cast hdN
  rw [periodTail_eq_fraction T K c hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1]
  apply (div_le_div_iff₀ hs hd).mpr
  have hR : (q : ℝ) * periodTailDenominator T K c ≤
      (scale : ℝ) * (periodTailNumerator T K c : ℝ) := by exact_mod_cast hh.2.2.2.2.2
  simpa only [mul_comm] using hR

def tailBlockCheck (scale T K : ℕ) : List TwentyEightCellCertificate → List ℕ → Bool
  | [], [] => true
  | c :: cs, q :: qs => tailFloorCheck scale T K c q && tailBlockCheck scale T K cs qs
  | _, _ => false

theorem tailBlockCheck_sound (scale T K : ℕ) (cs : List TwentyEightCellCertificate)
    (qs : List ℕ) (h : tailBlockCheck scale T K cs qs = true) :
    (qs.sum : ℝ) / scale ≤ (cs.map (fun c => (periodTailRational T K c : ℝ))).sum := by
  induction cs generalizing qs with
  | nil =>
    cases qs with
    | nil => simp
    | cons q qs => simp [tailBlockCheck] at h
  | cons c cs ih =>
    cases qs with
    | nil => simp [tailBlockCheck] at h
    | cons q qs =>
      have hh : tailFloorCheck scale T K c q = true ∧ tailBlockCheck scale T K cs qs = true := by
        simpa only [tailBlockCheck, Bool.and_eq_true] using h
      have ht := tailFloorCheck_sound scale T K c q hh.1
      have hr := ih qs hh.2
      simpa only [List.sum_cons, List.map_cons, Nat.cast_add, add_div] using add_le_add ht hr

end OddPiPowers.L99.PrimeRates
