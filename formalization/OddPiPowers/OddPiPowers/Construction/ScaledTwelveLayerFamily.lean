module

public import OddPiPowers.Arithmetic.TwelveLayerFamily
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.EquivFin

/-! Draft scaled actual twelve-layer interval family and carry grouping.
This file was not compiled by the helper. -/

@[expose] public section

namespace OddPiPowers

set_option backward.isDefEq.respectTransparency false

def scaledTwelveLayerOffset (s : ℕ) (a : Fin (17 * s)) : ℕ :=
  if a.val < 6 * s then 0 else (a.val - 6 * s) / s + 1

theorem scaledTwelveLayerOffset_le_eleven (s : ℕ) (hs : 0 < s)
    (a : Fin (17 * s)) : scaledTwelveLayerOffset s a ≤ 11 := by
  unfold scaledTwelveLayerOffset
  split_ifs with ha
  · omega
  · have halt : a.val < 17 * s := a.isLt
    have hd : a.val - 6 * s < 11 * s := by omega
    have hq : (a.val - 6 * s) / s < 11 := by
      apply (Nat.div_lt_iff_lt_mul hs).2
      simpa [Nat.mul_comm] using hd
    omega

theorem scaledTwelveLayerOffset_mono (s : ℕ) :
    Monotone (scaledTwelveLayerOffset s) := by
  intro a b hab
  have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
  unfold scaledTwelveLayerOffset
  by_cases ha : a.val < 6 * s
  · simp [ha]
  · have hb : ¬ b.val < 6 * s := by omega
    simp only [ha, hb, ite_false]
    exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1

def scaledTwelveLayerActualFamily (s : ℕ) (hs : 0 < s) (N : ℕ) :
    ActualIntervals (17 * s) where
  n := 69 * N
  left := fun a => scaledTwelveLayerOffset s a * N
  left_mono := by
    intro a b hab
    exact Nat.mul_le_mul_right N (scaledTwelveLayerOffset_mono s hab)
  left_bound := by
    intro a
    have ho := scaledTwelveLayerOffset_le_eleven s hs a
    calc
      2 * (scaledTwelveLayerOffset s a * N) =
          (2 * scaledTwelveLayerOffset s a) * N := by rw [Nat.mul_assoc]
      _ ≤ 69 * N := Nat.mul_le_mul_right N (by omega)

theorem scaledTwelveLayerActualFamily_n_eq (s : ℕ) (hs : 0 < s) (N : ℕ) :
    (scaledTwelveLayerActualFamily s hs N).n = 69 * N := rfl

theorem scaledTwelveLayerActualFamily_left_scaled (s : ℕ) (hs : 0 < s)
    (N : ℕ) (a : Fin (17 * s)) :
    (scaledTwelveLayerActualFamily s hs N).left a = scaledTwelveLayerOffset s a * N := rfl

/-- The six-fold zero layer precedes eleven fibers of size `s`. -/
def scaledTwelveLayerIndexToSigma (s : ℕ) (hs : 0 < s) (a : Fin (17 * s)) :
    Σ j : Fin 12, Fin (s * (if j.val = 0 then 6 else 1)) :=
  if ha : a.val < 6 * s then
    ⟨⟨0, by omega⟩, ⟨a.val, by
      simpa [CarryShape.scaleWeights, twelveLayerShape, Nat.mul_comm] using ha⟩⟩
  else
    ⟨⟨(a.val - 6 * s) / s + 1, by
      have hd : a.val - 6 * s < 11 * s := by have := a.isLt; omega
      have hq : (a.val - 6 * s) / s < 11 := by
        apply (Nat.div_lt_iff_lt_mul hs).2
        simpa [Nat.mul_comm] using hd
      omega⟩,
     ⟨(a.val - 6 * s) % s, by
      have hne : (a.val - 6 * s) / s + 1 ≠ 0 := Nat.succ_ne_zero _
      simpa [CarryShape.scaleWeights, twelveLayerShape, hne] using
        Nat.mod_lt (a.val - 6 * s) hs⟩⟩

def scaledTwelveLayerSigmaToIndex (s : ℕ) (hs : 0 < s)
    (x : Σ j : Fin 12, Fin (s * (if j.val = 0 then 6 else 1))) :
    Fin (17 * s) :=
  if hx : x.1.val = 0 then
    ⟨x.2.val, by
      have hk : x.2.val < 6 * s := by
        simpa [CarryShape.scaleWeights, twelveLayerShape, hx, Nat.mul_comm] using x.2.isLt
      omega⟩
  else
    ⟨6 * s + (x.1.val - 1) * s + x.2.val, by
      have hk : x.2.val < s := by
        simpa [CarryShape.scaleWeights, twelveLayerShape, hx] using x.2.isLt
      have hj : x.1.val < 12 := x.1.isLt
      have hprod : (x.1.val - 1) * s ≤ 10 * s :=
        Nat.mul_le_mul_right s (by omega)
      omega⟩

theorem scaledTwelveLayer_leftInverse (s : ℕ) (hs : 0 < s) :
    Function.LeftInverse (scaledTwelveLayerSigmaToIndex s hs)
      (scaledTwelveLayerIndexToSigma s hs) := by
    intro a
    unfold scaledTwelveLayerIndexToSigma
    split
    · apply Fin.ext
      rfl
    · apply Fin.ext
      rename_i ha
      have hdiv := Nat.div_add_mod (a.val - 6 * s) s
      have hz : (a.val - 6 * s) / s + 1 ≠ 0 := Nat.succ_ne_zero _
      dsimp only [scaledTwelveLayerSigmaToIndex]
      simp only [
        dite_eq_right hz, Nat.add_sub_cancel]
      have hcomm : (a.val - 6 * s) / s * s = s * ((a.val - 6 * s) / s) := Nat.mul_comm _ _
      omega

noncomputable def scaledTwelveLayerIndexEquiv (s : ℕ) (hs : 0 < s) :
    Fin (17 * s) ≃ Σ j : Fin 12, Fin (s * (if j.val = 0 then 6 else 1)) :=
  Equiv.ofBijective (scaledTwelveLayerIndexToSigma s hs)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨
      (scaledTwelveLayer_leftInverse s hs).injective, by
        simp only [Fintype.card_fin, Fintype.card_sigma]
        simp [Fin.sum_univ_succ]
        omega⟩)

noncomputable def scaledTwelveLayerActualGrouping (s : ℕ) (hs : 0 < s) (N : ℕ) :
    ActualIntervals.ActualCarryGrouping (scaledTwelveLayerActualFamily s hs N)
      (twelveLayerShape.scaleWeights s) N where
  indexEquiv := scaledTwelveLayerIndexEquiv s hs
  n_eq := rfl
  left_eq := by
    intro a
    change scaledTwelveLayerOffset s a * N =
      (scaledTwelveLayerIndexToSigma s hs a).1.val * N
    by_cases ha : a.val < 6 * s <;>
      simp [scaledTwelveLayerOffset, scaledTwelveLayerIndexToSigma, ha,
        CarryShape.scaleWeights, twelveLayerShape]

end OddPiPowers
