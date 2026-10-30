module

public import OddPiPowers.Transfer.AuxiliaryFamily
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

/-! Elementary comparison of a small value and a nonzero algebraic value. -/

@[expose] public section

namespace OddPiPowers

/-- This form never divides by the divided difference, which may be zero. -/
theorem small_value_forces_distance (x y ux uy t : ℂ) (a H : ℝ)
    (hH : 0 < H) (hid : ux - uy = (x - y) * t)
    (hsmall : ‖ux‖ ≤ a / 2) (hbig : a ≤ ‖uy‖) (ht : ‖t‖ ≤ H) :
    a / (2 * H) ≤ ‖x - y‖ := by
  have htriangle : ‖uy‖ ≤ ‖ux - uy‖ + ‖ux‖ := by
    have heq : (ux - uy) - ux = -uy := by ring
    simpa only [heq, norm_neg] using norm_sub_le (ux - uy) ux
  have hdiff : ‖ux - uy‖ ≤ ‖x - y‖ * H := by
    rw [hid, norm_mul]
    gcongr
  have hhalf : a / 2 ≤ ‖x - y‖ * H := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * H)).2
  nlinarith

end OddPiPowers
