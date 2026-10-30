module

public import OddPiPowers.Analysis.ActualReducedFamily
public import OddPiPowers.L99.Construction.ScaledTwentyEightLayerFamily

/-! Reindex the actual scaled construction by the twentyEight layers. -/

@[expose] public section

namespace OddPiPowers.L99

open scoped BigOperators

theorem scaledTwentyEightLayerIndexEquiv_offset (s : ℕ) (hs : 0 < s) (a : Fin (43 * s)) :
    (scaledTwentyEightLayerIndexEquiv s hs a).1.val = scaledTwentyEightLayerOffset s a := by
  change (scaledTwentyEightLayerIndexToSigma s hs a).1.val = _
  unfold scaledTwentyEightLayerIndexToSigma scaledTwentyEightLayerOffset
  split <;> rfl

theorem scaledTwentyEightLayer_sum_offset (s : ℕ) (hs : 0 < s) (f : ℕ → ℝ) :
    (∑ a : Fin (43 * s), f (scaledTwentyEightLayerOffset s a)) =
      (s : ℝ) * (16 * f 0 + ∑ j : Fin 27, f (j.val + 1)) := by
  classical
  have he := (scaledTwentyEightLayerIndexEquiv s hs).sum_comp
    (fun x : Σ j : Fin 28, Fin (s * (if j.val = 0 then 16 else 1)) => f x.1.val)
  simp only [scaledTwentyEightLayerIndexEquiv_offset] at he
  rw [he, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, ite_true, Nat.cast_mul, Nat.cast_ofNat, Fin.val_succ,
    Nat.succ_ne_zero, ite_false, Nat.mul_one]
  rw [mul_add, Finset.mul_sum]
  ring

theorem scaledTwentyEightLayer_shapeRelativeLength (s : ℕ) (hs : 0 < s) :
    shapeRelativeLength 99 (scaledTwentyEightLayerOffset s) = (s : ℝ) * (389 / 11) := by
  unfold shapeRelativeLength
  norm_num only [Nat.cast_ofNat]
  rw [scaledTwentyEightLayer_sum_offset s hs
    (fun j => (((99 - 2 * j : ℕ) : ℝ) / 99))]
  norm_num [Fin.sum_univ_succ]

theorem scaledTwentyEightLayer_central_sum (s : ℕ) (hs : 0 < s) (Y : ℝ) :
    (∑ a : Fin (43 * s), centralIntervalRate
      (((99 - 2 * scaledTwentyEightLayerOffset s a : ℕ) : ℝ) / 99) Y) =
    (s : ℝ) * (16 * centralIntervalRate 1 Y +
      ∑ j : Fin 27, centralIntervalRate (((97 - 2 * j.val : ℕ) : ℝ) / 99) Y) := by
  rw [scaledTwentyEightLayer_sum_offset s hs
    (fun j => centralIntervalRate (((99 - 2 * j : ℕ) : ℝ) / 99) Y)]
  congr 2
  norm_num

end OddPiPowers.L99
