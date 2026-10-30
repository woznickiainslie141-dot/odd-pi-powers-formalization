module

public import OddPiPowers.L99.Arithmetic.PeriodFloorCertificate

/-! Linear-size certificate checking without rational common denominators. -/

@[expose] public section

namespace OddPiPowers.L99.PrimeRates

open OddPiPowers.PrimeRates

abbrev PeriodLabel := TwentyEightCellCertificate × ℕ

noncomputable def periodLabelActual (p : PeriodLabel) : ℝ :=
  (p.1.value : ℝ) / 99 * periodGap p.2 (p.1.left : ℝ) (p.1.right : ℝ)

def periodBlockCheck (scale : ℕ) : List PeriodLabel → List ℕ → Bool
  | [], [] => true
  | p :: labels, q :: floors =>
      periodFloorCheck scale ⟨p.1, p.2, q⟩ && periodBlockCheck scale labels floors
  | _, _ => false

theorem periodBlockCheck_sound (scale : ℕ) (labels : List PeriodLabel) (floors : List ℕ)
    (hc : periodBlockCheck scale labels floors = true) :
    (floors.sum : ℝ) / scale ≤ (labels.map periodLabelActual).sum := by
  induction labels generalizing floors with
  | nil =>
    cases floors with
    | nil => simp
    | cons q qs => simp [periodBlockCheck] at hc
  | cons p labels ih =>
    cases floors with
    | nil => simp [periodBlockCheck] at hc
    | cons q qs =>
      have hall : periodFloorCheck scale ⟨p.1, p.2, q⟩ = true ∧
          periodBlockCheck scale labels qs = true := by
        simpa only [periodBlockCheck, Bool.and_eq_true] using hc
      have ht := periodFloorCheck_sound scale ⟨p.1, p.2, q⟩ hall.1
      have hr := ih qs hall.2
      simpa only [List.sum_cons, List.map_cons, Nat.cast_add, add_div,
        periodLabelActual, periodFloorActual] using add_le_add ht hr

def periodPrefixLabels (T : ℕ) (cells : List TwentyEightCellCertificate) : List PeriodLabel :=
  cells.flatMap (fun c => (List.range T).map (fun r => (c, r)))

end OddPiPowers.L99.PrimeRates
