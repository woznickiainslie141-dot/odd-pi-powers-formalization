module

public import OddPiPowers.Analysis.RectanglePrimitives

/-! Higher inverse powers have a primitive along the boundary, even when
their pole lies inside the rectangle. -/

@[expose] public section

namespace OddPiPowers

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_inversePower_primitive (p : ℝ) (j : ℕ) (z : ℂ) (hz : z ≠ (p : ℂ)) :
    HasDerivAt (fun w : ℂ => -((w - (p : ℂ)) ^ (j + 1))⁻¹ / ((j + 1 : ℕ) : ℂ))
      (1 / (z - (p : ℂ)) ^ (j + 2)) z := by
  have hn : z - (p : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  have hk : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hh := (((hasDerivAt_id z).sub_const (p : ℂ)).pow (j + 1)).inv (pow_ne_zero _ hn)
  have hh' : HasDerivAt (fun w : ℂ => -((w - (p : ℂ)) ^ (j + 1))⁻¹ / ((j + 1 : ℕ) : ℂ))
      (-(-((((j + 1 : ℕ) : ℂ)) * (z - (p : ℂ)) ^ j) /
        ((z - (p : ℂ)) ^ (j + 1)) ^ 2) / ((j + 1 : ℕ) : ℂ)) z := by
    simpa only [Pi.div_apply, Pi.neg_apply, Pi.inv_apply, Pi.pow_apply, id_eq,
      Nat.add_sub_cancel, mul_one] using hh.neg.div_const (((j + 1 : ℕ) : ℂ))
  convert hh' using 1
  field_simp [pow_succ, hn, hk]
  ring

theorem rectangleIntegral_higher_inverse (p a b c d : ℝ)
    (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ 0) (hd : d ≠ 0) (j : ℕ) :
    rectangleIntegral (fun z : ℂ => 1 / (z - (p : ℂ)) ^ (j + 2)) a b c d = 0 := by
  apply rectangleIntegral_eq_zero_of_boundary_primitive
    (fun w : ℂ => -((w - (p : ℂ)) ^ (j + 1))⁻¹ / ((j + 1 : ℕ) : ℂ))
    (fun z : ℂ => 1 / (z - (p : ℂ)) ^ (j + 2)) a b c d
    (rectangleIntegrable_pole (fun _ : ℂ => 1) continuous_const p a b c d ha hb hc hd (j + 2))
  · intro x hx
    exact hasDerivAt_inversePower_primitive p j _
      (sub_ne_zero.mp (rectangle_horizontal_ne_pole p c x hc))
  · intro x hx
    exact hasDerivAt_inversePower_primitive p j _
      (sub_ne_zero.mp (rectangle_horizontal_ne_pole p d x hd))
  · intro y hy
    exact hasDerivAt_inversePower_primitive p j _
      (sub_ne_zero.mp (rectangle_vertical_ne_pole p b y hb))
  · intro y hy
    exact hasDerivAt_inversePower_primitive p j _
      (sub_ne_zero.mp (rectangle_vertical_ne_pole p a y ha))

end OddPiPowers
