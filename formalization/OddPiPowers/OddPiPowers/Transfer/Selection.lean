module

public import OddPiPowers.Transfer.NonzeroRow
public import OddPiPowers.Transfer.RationalPower

/-! Select a row and apply the uniform algebraic-value estimate. -/

@[expose] public section

namespace OddPiPowers

open Polynomial

theorem exists_row_rational_value_lower_bound (p : ℤ) (q k : ℕ)
    (hq : 0 < q) (hk : 0 < k) (θ : ℝ) (hθ : θ ^ k = (p : ℝ) / q)
    (hyDisk : ‖Complex.I * (θ : ℂ) / 2‖ ≤ 2) (m : ℕ)
    (U : Fin (m + 1) → GaussianInt[X]) (hdeg : ∀ i, (U i).natDegree ≤ m)
    (hdet : (coefficientMatrix m U).det ≠ 0) (H : NNReal) (hH : 1 ≤ H)
    (hheight : ∀ i z, ‖z‖ ≤ 2 → ‖((U i).map GaussianInt.toComplex).eval z‖₊ ≤ H) :
    ∃ i, 1 / (((2 : NNReal) ^ k * q) ^ m * H ^ (k - 1)) ≤
      ‖((U i).map GaussianInt.toComplex).eval (Complex.I * (θ : ℂ) / 2)‖₊ := by
  obtain ⟨i, hi⟩ := exists_polynomial_nonzero_row m U hdeg hdet
    (Complex.I * (θ : ℂ) / 2)
  exact ⟨i, rational_power_value_lower_bound p q k hq hk θ hθ hyDisk (U i) hi
    m (hdeg i) H hH (hheight i)⟩

end OddPiPowers
