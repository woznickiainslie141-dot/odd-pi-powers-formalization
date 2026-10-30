module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

/-! Discreteness of the Gaussian integer lattice in `ℂ`. -/

@[expose] public section

namespace OddPiPowers

/-- The Gaussian integer whose complex image is the imaginary unit. -/
def gaussianI : GaussianInt := ⟨0, 1⟩

@[simp] theorem gaussianI_toComplex : (gaussianI : ℂ) = Complex.I := by
  simp [gaussianI, GaussianInt.toComplex_def']

theorem gaussian_norm_ge_one (z : GaussianInt) (hz : z ≠ 0) : 1 ≤ ‖(z : ℂ)‖ := by
  have hInt : (1 : ℤ) ≤ z.norm := by
    exact Int.add_one_le_iff.mpr (GaussianInt.norm_pos.mpr hz)
  have hReal : (1 : ℝ) ≤ (z.norm : ℝ) := by exact_mod_cast hInt
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at hReal
  nlinarith [norm_nonneg (z : ℂ)]

/-- A nonzero Gaussian multiple has modulus at least that of its divisor. -/
theorem gaussian_nnnorm_le_of_dvd {a b : GaussianInt} (hb : b ≠ 0) (hab : a ∣ b) :
    ‖(a : ℂ)‖₊ ≤ ‖(b : ℂ)‖₊ := by
  obtain ⟨c, rfl⟩ := hab
  have hc : c ≠ 0 := by
    intro hz
    apply hb
    simp [hz]
  have hc1 : (1 : NNReal) ≤ ‖(c : ℂ)‖₊ := by
    exact_mod_cast gaussian_norm_ge_one c hc
  calc
    ‖(a : ℂ)‖₊ = ‖(a : ℂ)‖₊ * 1 := by simp
    _ ≤ ‖(a : ℂ)‖₊ * ‖(c : ℂ)‖₊ := by gcongr
    _ = ‖((a * c : GaussianInt) : ℂ)‖₊ := by rw [GaussianInt.toComplex_mul, nnnorm_mul]

end OddPiPowers
