module

public import OddPiPowers.Arithmetic.ScaledPrimeRates
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Draft symbolic finite-period wrapper for accepted carry-cell windows.
This file has not been compiled by the helper. -/

@[expose] public section

open scoped BigOperators Topology

namespace OddPiPowers.PrimeRates

set_option backward.isDefEq.respectTransparency false

/-- Copy a template's cell and interior endpoints into a chosen period. -/
def CertifiedCellWindow.atPeriod (V : CertifiedCellWindow) (r : ℕ) : CertifiedCellWindow :=
  { V with period := r }

variable {ι : Type*} [DecidableEq ι]

def periodWindowIndices (K : ℕ) (s : Finset ι) : Finset (ℕ × ι) :=
  (Finset.range K).product s

def periodWindowFamily (V : ι → CertifiedCellWindow) (p : ℕ × ι) : CertifiedCellWindow :=
  (V p.2).atPeriod p.1

theorem periodWindowFamily_labels_inj (K : ℕ) (s : Finset ι)
    (V : ι → CertifiedCellWindow)
    (hcell_inj : Set.InjOn (fun i => (V i).cell) ↑s) :
    Set.InjOn (fun p => ((periodWindowFamily V p).period, (periodWindowFamily V p).cell))
      ↑(periodWindowIndices K s) := by
  intro p hp q hq heq
  have hp' : p.1 ∈ Finset.range K ∧ p.2 ∈ s := Finset.mem_product.mp hp
  have hq' : q.1 ∈ Finset.range K ∧ q.2 ∈ s := Finset.mem_product.mp hq
  have hr : p.1 = q.1 := by
    simpa [periodWindowFamily, CertifiedCellWindow.atPeriod] using congrArg Prod.fst heq
  have hc : (V p.2).cell = (V q.2).cell := by
    simpa [periodWindowFamily, CertifiedCellWindow.atPeriod] using congrArg Prod.snd heq
  have hi : p.2 = q.2 := hcell_inj hp'.2 hq'.2 hc
  exact Prod.ext hr hi

theorem periodWindowFamily_cap (K : ℕ) (s : Finset ι)
    (V : ι → CertifiedCellWindow)
    (hcap : ∀ i ∈ s, 1 ≤ (69 : ℝ) * (V i).a) :
    ∀ p ∈ periodWindowIndices K s,
      1 ≤ (69 : ℝ) * (periodWindowFamily V p).toWindow.lower := by
  intro p hp
  have hi : p.2 ∈ s := (Finset.mem_product.mp hp).2
  have hn : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg p.1
  have hc := hcap p.2 hi
  change 1 ≤ (69 : ℝ) * ((p.1 : ℝ) + (V p.2).a)
  linarith

noncomputable def periodWindowRate (K : ℕ) (s : Finset ι)
    (V : ι → CertifiedCellWindow) : ℝ :=
  (1 / 69 : ℝ) * ∑ r ∈ Finset.range K, ∑ i ∈ s,
    ((V i).cell.value : ℝ) * periodGap r (V i).a (V i).b

theorem periodWindowFamily_rate (K : ℕ) (s : Finset ι)
    (V : ι → CertifiedCellWindow) :
    finiteWindowRate (periodWindowIndices K s)
      (fun p => (periodWindowFamily V p).toWindow) 69 = periodWindowRate K s V := by
  classical
  unfold finiteWindowRate periodWindowRate periodWindowIndices
  simp only [CertifiedCellWindow.rate_identity]
  have he := Finset.sum_product (Finset.range K) s
    (fun p : ℕ × ι => ((periodWindowFamily V p).cell.value : ℝ) *
      periodGap (periodWindowFamily V p).period (periodWindowFamily V p).a
        (periodWindowFamily V p).b)
  calc
    _ = (∑ r ∈ Finset.range K, ∑ i ∈ s,
        ((periodWindowFamily V (r, i)).cell.value : ℝ) *
          periodGap (periodWindowFamily V (r, i)).period
            (periodWindowFamily V (r, i)).a (periodWindowFamily V (r, i)).b) / 69 :=
      congrArg (fun x : ℝ => x / 69) he
    _ = _ := by simp only [periodWindowFamily, CertifiedCellWindow.atPeriod]; ring

/-- PNT and the actual coefficient divisor apply to the symbolic finite set
of all template windows in periods `r < K`. -/
theorem periodWindowFamily_scaled_actualDivisor_eventually_exp_lower
    (K : ℕ) (s : Finset ι) (V : ι → CertifiedCellWindow)
    (hcell_inj : Set.InjOn (fun i => (V i).cell) ↑s)
    (hcap : ∀ i ∈ s, 1 ≤ (69 : ℝ) * (V i).a)
    (u : ℕ) {M : ℕ} (P : ℕ → ActualIntervals M)
    (G : ∀ N, ActualIntervals.ActualCarryGrouping (P N) (twelveLayerShape.scaleWeights u) N)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (((u : ℝ) * periodWindowRate K s V - η) * (69 * N : ℕ)) ≤
        ((P N).actualAuxiliaryPrimeDivisor : ℝ) := by
  have h := twelveLayer_scaled_actualDivisor_eventually_exp_lower
    (periodWindowIndices K s) (periodWindowFamily V)
    (periodWindowFamily_labels_inj K s V hcell_inj)
    (periodWindowFamily_cap K s V hcap) u P G hη
  simpa only [periodWindowFamily_rate] using h

end OddPiPowers.PrimeRates
