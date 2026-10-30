module

public import OddPiPowers.Arithmetic.CertifiedPrimeDivisor
public import OddPiPowers.Arithmetic.TwelveLayerCellDefs
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace OddPiPowers

/-- A concrete family of 17 nested intervals realizing the twelve-layer
shape at scale `N`. The first six intervals are the six copies of offset 0. -/
def twelveLayerActualFamily (N : ℕ) : ActualIntervals 17 where
  n := 69 * N
  left := fun a => if a.val < 6 then 0 else (a.val - 5) * N
  left_mono := by
    intro a b hab
    have habVal : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
    change (if a.val < 6 then 0 else (a.val - 5) * N) ≤
      (if b.val < 6 then 0 else (b.val - 5) * N)
    by_cases ha : a.val < 6
    · simp [ha]
    · have hb : ¬ b.val < 6 := by omega
      simp [ha, hb]
      exact Nat.mul_le_mul_right N (by omega : a.val - 5 ≤ b.val - 5)
  left_bound := by
    intro a
    change 2 * (if a.val < 6 then 0 else (a.val - 5) * N) ≤ 69 * N
    by_cases ha : a.val < 6
    · simp [ha]
    · have ha_lt : a.val < 17 := a.isLt
      have hfactor : 2 * (a.val - 5) ≤ 69 := by omega
      simp only [if_neg ha]
      calc
        2 * ((a.val - 5) * N) = (2 * (a.val - 5)) * N := by
          rw [← Nat.mul_assoc]
        _ ≤ 69 * N := Nat.mul_le_mul_right N hfactor

/-- Map the first six indices to the six-element fiber over offset zero;
the remaining eleven indices map one each to offsets 1 through 11. -/
def twelveLayerIndexToSigma (a : Fin 17) :
    Σ j : Fin 12, Fin (twelveLayerShape.weight j) :=
  if ha : a.val < 6 then
    ⟨⟨0, by omega⟩,
      ⟨a.val, by simpa [twelveLayerShape] using ha⟩⟩
  else
    ⟨⟨a.val - 5, by have ha_lt := a.isLt; omega⟩,
      ⟨0, by
        have hne : a.val - 5 ≠ 0 := by omega
        simp [twelveLayerShape, hne]⟩⟩

/-- The inverse sends the six-element zero-offset fiber back to `0,...,5`
and the remaining singleton fibers back to `6,...,16`. -/
def twelveLayerSigmaToIndex
    (x : Σ j : Fin 12, Fin (twelveLayerShape.weight j)) : Fin 17 :=
  if hx : x.1.val = 0 then
    ⟨x.2.val, by
      have hk : x.2.val < 6 := by
        simpa [twelveLayerShape, hx] using x.2.isLt
      omega⟩
  else
    ⟨x.1.val + 5, by have hj_lt := x.1.isLt; omega⟩

def twelveLayerIndexEquiv :
    Fin 17 ≃ Σ j : Fin 12, Fin (twelveLayerShape.weight j) where
  toFun := twelveLayerIndexToSigma
  invFun := twelveLayerSigmaToIndex
  left_inv := by
    intro a
    fin_cases a <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;>
      simp [twelveLayerIndexToSigma, twelveLayerSigmaToIndex, twelveLayerShape]

/-- The 17 actual intervals have exactly the prescribed twelve-layer
grouping, including the six copies of the first layer. -/
def twelveLayerActualGrouping (N : ℕ) :
    ActualIntervals.ActualCarryGrouping
      (twelveLayerActualFamily N) twelveLayerShape N where
  indexEquiv := twelveLayerIndexEquiv
  n_eq := by
    rfl
  left_eq := by
    intro a
    change (if a.val < 6 then 0 else (a.val - 5) * N) =
      (twelveLayerIndexToSigma a).1.val * N
    fin_cases a <;> norm_num [twelveLayerIndexToSigma]

end OddPiPowers

end
