module

public import OddPiPowers.Construction.ActualAuxiliary
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Ring

/-! Algebraic expansion of the actual exponential remainder.

The helper draft was checked by the main chat under the bounded runner.
The local expansion already contains the interval-length factorials. -/

@[expose] public section

namespace OddPiPowers

noncomputable def actualExponentialRemainder {M : ℕ}
    (P : ActualIntervals M) (h : Fin M) (lambda : ℂ) : ℂ :=
  ∑ j : Fin M, (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ)
    (Complex.exp lambda) * lambda ^ j.val

theorem actualAuxiliary_eval_exp {M : ℕ} (P : ActualIntervals M)
    (h j : Fin M) (lambda : ℂ) :
    (actualAuxiliary P h j).eval₂ (Rat.castHom ℂ) (Complex.exp lambda) =
      ∑ ell ∈ Finset.range (P.n + 1),
        ((auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val : ℚ) : ℂ) *
          Complex.exp (lambda * ((P.n : ℂ) - (ell : ℂ))) := by
  rw [actualAuxiliary, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_X]
  apply Finset.sum_congr rfl
  intro ell hell
  have helln : ell ≤ P.n := by
    have := Finset.mem_range.mp hell
    omega
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast [Nat.cast_sub helln]
  ring

theorem actualExponentialRemainder_eq_sum {M : ℕ}
    (P : ActualIntervals M) (h : Fin M) (lambda : ℂ) :
    actualExponentialRemainder P h lambda =
      ∑ ell ∈ Finset.range (P.n + 1), ∑ j : Fin M,
        ((auxiliaryScale M P.n j.val * P.localCoefficient ell h.val j.val : ℚ) : ℂ) *
          Complex.exp (lambda * ((P.n : ℂ) - (ell : ℂ))) * lambda ^ j.val := by
  unfold actualExponentialRemainder
  simp_rw [actualAuxiliary_eval_exp, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Reindex the local expansion by derivative order. The proof includes the
case of zero multiplicity and makes no distinctness assumption on endpoints. -/
theorem localCoefficient_reflection {M : ℕ} (P : ActualIntervals M)
    (ell h : ℕ) (weight : ℕ → ℂ) (hμM : P.multiplicity ell ≤ M) :
    (∑ q ∈ Finset.range (P.multiplicity ell),
      ((PowerSeries.coeff q (P.localExpansion ell h) : ℚ) : ℂ) *
        weight (P.multiplicity ell - 1 - q)) =
      ∑ j : Fin M, ((P.localCoefficient ell h j.val : ℚ) : ℂ) * weight j.val := by
  classical
  let μ := P.multiplicity ell
  let f : ℕ → ℂ := fun j =>
    ((PowerSeries.coeff (μ - 1 - j) (P.localExpansion ell h) : ℚ) : ℂ) * weight j
  let g : ℕ → ℂ := fun j => ((P.localCoefficient ell h j : ℚ) : ℂ) * weight j
  have hreflect : (∑ q ∈ Finset.range μ, f (μ - 1 - q)) =
      ∑ j ∈ Finset.range μ, f j := Finset.sum_range_reflect f μ
  have hleft : (∑ q ∈ Finset.range μ,
      ((PowerSeries.coeff q (P.localExpansion ell h) : ℚ) : ℂ) *
        weight (μ - 1 - q)) = ∑ q ∈ Finset.range μ, f (μ - 1 - q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q < μ := Finset.mem_range.mp hq
    have hinv : μ - 1 - (μ - 1 - q) = q := by omega
    simp [f, hinv]
  have hsmall : (∑ j ∈ Finset.range μ, f j) = ∑ j ∈ Finset.range μ, g j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < P.multiplicity ell := Finset.mem_range.mp hj
    simp [f, g, μ, ActualIntervals.localCoefficient, hjlt]
  have hlarge : (∑ j ∈ Finset.range μ, g j) = ∑ j ∈ Finset.range M, g j := by
    apply Finset.sum_subset (Finset.range_mono hμM)
    intro j hjM hjμ
    have hjge : μ ≤ j := by
      have hn : ¬ j < μ := by simpa using hjμ
      omega
    have hn : ¬ j < P.multiplicity ell := by simpa [μ] using (Nat.not_lt.mpr hjge)
    simp [g, ActualIntervals.localCoefficient, hn]
  change (∑ q ∈ Finset.range μ,
      ((PowerSeries.coeff q (P.localExpansion ell h) : ℚ) : ℂ) *
        weight (μ - 1 - q)) = ∑ j : Fin M, g j.val
  rw [hleft, hreflect, hsmall, hlarge, ← Fin.sum_univ_eq_sum_range g M]

end OddPiPowers
