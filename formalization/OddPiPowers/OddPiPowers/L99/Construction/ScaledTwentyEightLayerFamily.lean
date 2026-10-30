module

public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs
public import OddPiPowers.Arithmetic.CertifiedPrimeDivisor
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.EquivFin

/-! Draft scaled actual twentyEight-layer interval family and carry grouping.
This file was not compiled by the helper. -/

@[expose] public section

namespace OddPiPowers.L99

set_option backward.isDefEq.respectTransparency false

def scaledTwentyEightLayerOffset (s : ℕ) (a : Fin (43 * s)) : ℕ :=
  if a.val < 16 * s then 0 else (a.val - 16 * s) / s + 1

theorem scaledTwentyEightLayerOffset_le_twentySeven (s : ℕ) (hs : 0 < s)
    (a : Fin (43 * s)) : scaledTwentyEightLayerOffset s a ≤ 27 := by
  unfold scaledTwentyEightLayerOffset
  split_ifs with ha
  · omega
  · have halt : a.val < 43 * s := a.isLt
    have hd : a.val - 16 * s < 27 * s := by omega
    have hq : (a.val - 16 * s) / s < 27 := by
      apply (Nat.div_lt_iff_lt_mul hs).2
      simpa [Nat.mul_comm] using hd
    omega

theorem scaledTwentyEightLayerOffset_mono (s : ℕ) :
    Monotone (scaledTwentyEightLayerOffset s) := by
  intro a b hab
  have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
  unfold scaledTwentyEightLayerOffset
  by_cases ha : a.val < 16 * s
  · simp [ha]
  · have hb : ¬ b.val < 16 * s := by omega
    simp only [ha, hb, ite_false]
    exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1

def scaledTwentyEightLayerActualFamily (s : ℕ) (hs : 0 < s) (N : ℕ) :
    ActualIntervals (43 * s) where
  n := 99 * N
  left := fun a => scaledTwentyEightLayerOffset s a * N
  left_mono := by
    intro a b hab
    exact Nat.mul_le_mul_right N (scaledTwentyEightLayerOffset_mono s hab)
  left_bound := by
    intro a
    have ho := scaledTwentyEightLayerOffset_le_twentySeven s hs a
    calc
      2 * (scaledTwentyEightLayerOffset s a * N) =
          (2 * scaledTwentyEightLayerOffset s a) * N := by rw [Nat.mul_assoc]
      _ ≤ 99 * N := Nat.mul_le_mul_right N (by omega)

theorem scaledTwentyEightLayerActualFamily_n_eq (s : ℕ) (hs : 0 < s) (N : ℕ) :
    (scaledTwentyEightLayerActualFamily s hs N).n = 99 * N := rfl

theorem scaledTwentyEightLayerActualFamily_left_scaled (s : ℕ) (hs : 0 < s)
    (N : ℕ) (a : Fin (43 * s)) :
    (scaledTwentyEightLayerActualFamily s hs N).left a = scaledTwentyEightLayerOffset s a * N := rfl

/-- The six-fold zero layer precedes twentySeven fibers of size `s`. -/
def scaledTwentyEightLayerIndexToSigma (s : ℕ) (hs : 0 < s) (a : Fin (43 * s)) :
    Σ j : Fin 28, Fin (s * (if j.val = 0 then 16 else 1)) :=
  if ha : a.val < 16 * s then
    ⟨⟨0, by omega⟩, ⟨a.val, by
      simpa [CarryShape.scaleWeights, twentyEightLayerShape, Nat.mul_comm] using ha⟩⟩
  else
    ⟨⟨(a.val - 16 * s) / s + 1, by
      have hd : a.val - 16 * s < 27 * s := by have := a.isLt; omega
      have hq : (a.val - 16 * s) / s < 27 := by
        apply (Nat.div_lt_iff_lt_mul hs).2
        simpa [Nat.mul_comm] using hd
      omega⟩,
     ⟨(a.val - 16 * s) % s, by
      have hne : (a.val - 16 * s) / s + 1 ≠ 0 := Nat.succ_ne_zero _
      simpa [CarryShape.scaleWeights, twentyEightLayerShape, hne] using
        Nat.mod_lt (a.val - 16 * s) hs⟩⟩

def scaledTwentyEightLayerSigmaToIndex (s : ℕ) (hs : 0 < s)
    (x : Σ j : Fin 28, Fin (s * (if j.val = 0 then 16 else 1))) :
    Fin (43 * s) :=
  if hx : x.1.val = 0 then
    ⟨x.2.val, by
      have hk : x.2.val < 16 * s := by
        simpa [CarryShape.scaleWeights, twentyEightLayerShape, hx, Nat.mul_comm] using x.2.isLt
      omega⟩
  else
    ⟨16 * s + (x.1.val - 1) * s + x.2.val, by
      have hk : x.2.val < s := by
        simpa [CarryShape.scaleWeights, twentyEightLayerShape, hx] using x.2.isLt
      have hj : x.1.val < 28 := x.1.isLt
      have hprod : (x.1.val - 1) * s ≤ 26 * s :=
        Nat.mul_le_mul_right s (by omega)
      omega⟩

theorem scaledTwentyEightLayer_leftInverse (s : ℕ) (hs : 0 < s) :
    Function.LeftInverse (scaledTwentyEightLayerSigmaToIndex s hs)
      (scaledTwentyEightLayerIndexToSigma s hs) := by
    intro a
    unfold scaledTwentyEightLayerIndexToSigma
    split
    · apply Fin.ext
      rfl
    · apply Fin.ext
      rename_i ha
      have hdiv := Nat.div_add_mod (a.val - 16 * s) s
      have hz : (a.val - 16 * s) / s + 1 ≠ 0 := Nat.succ_ne_zero _
      dsimp only [scaledTwentyEightLayerSigmaToIndex]
      simp only [
        dite_eq_right hz, Nat.add_sub_cancel]
      have hcomm : (a.val - 16 * s) / s * s = s * ((a.val - 16 * s) / s) := Nat.mul_comm _ _
      omega

noncomputable def scaledTwentyEightLayerIndexEquiv (s : ℕ) (hs : 0 < s) :
    Fin (43 * s) ≃ Σ j : Fin 28, Fin (s * (if j.val = 0 then 16 else 1)) :=
  Equiv.ofBijective (scaledTwentyEightLayerIndexToSigma s hs)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨
      (scaledTwentyEightLayer_leftInverse s hs).injective, by
        simp only [Fintype.card_fin, Fintype.card_sigma]
        simp [Fin.sum_univ_succ]
        omega⟩)

noncomputable def scaledTwentyEightLayerActualGrouping (s : ℕ) (hs : 0 < s) (N : ℕ) :
    ActualIntervals.ActualCarryGrouping (scaledTwentyEightLayerActualFamily s hs N)
      (twentyEightLayerShape.scaleWeights s) N where
  indexEquiv := scaledTwentyEightLayerIndexEquiv s hs
  n_eq := rfl
  left_eq := by
    intro a
    change scaledTwentyEightLayerOffset s a * N =
      (scaledTwentyEightLayerIndexToSigma s hs a).1.val * N
    by_cases ha : a.val < 16 * s <;>
      simp [scaledTwentyEightLayerOffset, scaledTwentyEightLayerIndexToSigma, ha,
        CarryShape.scaleWeights, twentyEightLayerShape]

end OddPiPowers.L99
