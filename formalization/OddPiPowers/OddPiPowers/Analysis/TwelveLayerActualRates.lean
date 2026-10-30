module

public import OddPiPowers.Analysis.ActualReducedFamily
public import OddPiPowers.Construction.ScaledTwelveLayerFamily

/-! Reindex the actual scaled construction by the twelve layers. -/

@[expose] public section

namespace OddPiPowers

open scoped BigOperators

theorem scaledTwelveLayerIndexEquiv_offset (s : ℕ) (hs : 0 < s) (a : Fin (17 * s)) :
    (scaledTwelveLayerIndexEquiv s hs a).1.val = scaledTwelveLayerOffset s a := by
  change (scaledTwelveLayerIndexToSigma s hs a).1.val = _
  unfold scaledTwelveLayerIndexToSigma scaledTwelveLayerOffset
  split <;> rfl

theorem scaledTwelveLayer_sum_offset (s : ℕ) (hs : 0 < s) (f : ℕ → ℝ) :
    (∑ a : Fin (17 * s), f (scaledTwelveLayerOffset s a)) =
      (s : ℝ) * (6 * f 0 + ∑ j : Fin 11, f (j.val + 1)) := by
  classical
  have he := (scaledTwelveLayerIndexEquiv s hs).sum_comp
    (fun x : Σ j : Fin 12, Fin (s * (if j.val = 0 then 6 else 1)) => f x.1.val)
  simp only [scaledTwelveLayerIndexEquiv_offset] at he
  rw [he, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, ite_true, Nat.cast_mul, Nat.cast_ofNat, Fin.val_succ,
    Nat.succ_ne_zero, ite_false, Nat.mul_one]
  rw [mul_add, Finset.mul_sum]
  ring

theorem scaledTwelveLayer_shapeRelativeLength (s : ℕ) (hs : 0 < s) :
    shapeRelativeLength 69 (scaledTwelveLayerOffset s) = (s : ℝ) * (347 / 23) := by
  unfold shapeRelativeLength
  norm_num only [Nat.cast_ofNat]
  rw [scaledTwelveLayer_sum_offset s hs
    (fun j => (((69 - 2 * j : ℕ) : ℝ) / 69))]
  norm_num [Fin.sum_univ_succ]

theorem scaledTwelveLayer_central_sum (s : ℕ) (hs : 0 < s) (Y : ℝ) :
    (∑ a : Fin (17 * s), centralIntervalRate
      (((69 - 2 * scaledTwelveLayerOffset s a : ℕ) : ℝ) / 69) Y) =
    (s : ℝ) * (6 * centralIntervalRate 1 Y +
      ∑ j : Fin 11, centralIntervalRate (((67 - 2 * j.val : ℕ) : ℝ) / 69) Y) := by
  rw [scaledTwelveLayer_sum_offset s hs
    (fun j => centralIntervalRate (((69 - 2 * j : ℕ) : ℝ) / 69) Y)]
  congr 2
  norm_num

end OddPiPowers
