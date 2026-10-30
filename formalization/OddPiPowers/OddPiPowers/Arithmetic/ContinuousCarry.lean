module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace OddPiPowers

open scoped BigOperators

/-- The integer carry in the floor addition identity. -/
noncomputable def floorCarry (x y : ℝ) : ℤ := ⌊x + y⌋ - ⌊x⌋ - ⌊y⌋

theorem floorCarry_zero_or_one (x y : ℝ) :
    floorCarry x y = 0 ∨ floorCarry x y = 1 := by
  have hlo : ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ := Int.le_floor_add x y
  have hhi : ⌊x + y⌋ - 1 ≤ ⌊x⌋ + ⌊y⌋ := Int.le_floor_add_floor x y
  dsimp [floorCarry]
  omega

/-- The carry is determined by whether the two fractional parts cross one. -/
theorem floorCarry_eq_ite_frac_add (x y : ℝ) :
    floorCarry x y = if 1 ≤ Int.fract x + Int.fract y then 1 else 0 := by
  have hsum : x + y = (Int.fract x + Int.fract y) +
      (((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ)) := by
    calc
      x + y = ((⌊x⌋ : ℝ) + Int.fract x) + ((⌊y⌋ : ℝ) + Int.fract y) := by
        rw [Int.floor_add_fract x, Int.floor_add_fract y]
      _ = (Int.fract x + Int.fract y) + (((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ)) := by
        push_cast
        ring
  have hfloor : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + ⌊Int.fract x + Int.fract y⌋ := by
    rw [hsum, Int.floor_add_intCast]
    simp [add_assoc, add_comm, add_left_comm]
  have hfrac : ⌊Int.fract x + Int.fract y⌋ =
      if 1 ≤ Int.fract x + Int.fract y then 1 else 0 := by
    by_cases h : 1 ≤ Int.fract x + Int.fract y
    · rw [if_pos h]
      have hlo : (1 : ℝ) ≤ Int.fract x + Int.fract y := h
      have hhi : Int.fract x + Int.fract y < 2 := by
        have hx := Int.fract_lt_one x
        have hy := Int.fract_lt_one y
        have hx0 := Int.fract_nonneg x
        have hy0 := Int.fract_nonneg y
        linarith
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hlo
      · norm_num
        exact hhi
    · rw [if_neg h]
      have hx := Int.fract_lt_one x
      have hy := Int.fract_lt_one y
      have hx0 := Int.fract_nonneg x
      have hy0 := Int.fract_nonneg y
      have hlo : (0 : ℝ) ≤ Int.fract x + Int.fract y := by linarith
      have hhi : Int.fract x + Int.fract y < 1 := by linarith
      apply Int.floor_eq_iff.mpr
      exact ⟨by exact_mod_cast hlo, by simpa using hhi⟩
  unfold floorCarry
  rw [hfloor, hfrac]
  omega

/-- Euclidean division of a signed integer agrees with real floor division.
This is the bridge needed for negative interval-endpoint differences. -/
theorem floor_intCast_div_nat (x : ℤ) (n : ℕ) :
    ⌊(x : ℝ) / (n : ℝ)⌋ = x / (n : ℤ) := by
  rw [Int.floor_div_natCast]
  simp

/-- The fractional part represented using the integer floor. -/
noncomputable def realFrac (x : ℝ) : ℝ := Int.fract x

theorem realFrac_bounds (x : ℝ) : 0 ≤ realFrac x ∧ realFrac x < 1 := by
  constructor
  · exact Int.fract_nonneg x
  · exact Int.fract_lt_one x

theorem realFrac_add_intCast (x : ℝ) (n : ℤ) :
    realFrac (x + n) = realFrac x := by
  exact Int.fract_add_intCast x n

theorem floor_sub_unit_eq {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ⌊u - v⌋ = if u < v then -1 else 0 := by
  by_cases huv : u < v
  · rw [if_pos huv]
    have hlow : (-1 : ℝ) ≤ u - v := by linarith [hu0, hv1]
    have hhigh : u - v < 0 := by linarith
    apply Int.floor_eq_iff.mpr
    exact ⟨by exact_mod_cast hlow, by simpa using hhigh⟩
  · rw [if_neg huv]
    have hlow : 0 ≤ u - v := sub_nonneg.mpr (le_of_not_gt huv)
    have hhigh : u - v < 1 := by linarith [hu1, hv0]
    apply Int.floor_eq_iff.mpr
    exact ⟨by exact_mod_cast hlow, by simpa using hhigh⟩

theorem fract_sub_unit_eq {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Int.fract (u - v) = if u < v then u - v + 1 else u - v := by
  unfold Int.fract
  rw [floor_sub_unit_eq hu0 hu1 hv0 hv1]
  split_ifs <;> ring

/-- For unit endpoints, the carry is the signed jump across the two boundary
points. This identity keeps equality cases explicit. -/
theorem floorCarry_unitDifference (a y b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    floorCarry (y - a) (b - y) =
      (if y < a then 1 else 0) + (if b < y then 1 else 0) -
        (if b < a then 1 else 0) := by
  rw [floorCarry_eq_ite_frac_add,
    fract_sub_unit_eq hy0 hy1 ha0 ha1,
    fract_sub_unit_eq hb0 hb1 hy0 hy1]
  by_cases hya : y < a <;> by_cases hby : b < y <;> by_cases hba : b < a
  all_goals
    simp [hya, hby, hba]
    linarith

/-- A finite weighted family of the continuous carries from the arithmetic
section of the manuscript. -/
structure CarryShape where
  L : ℕ
  J : ℕ
  offset : Fin J → ℕ
  weight : Fin J → ℕ
  twoOffset_lt : ∀ j, 2 * offset j < L

namespace CarryShape

noncomputable def carry (C : CarryShape) (j : Fin C.J) (z y : ℝ) : ℤ :=
  floorCarry (y - (C.offset j : ℝ) * z)
    (((C.L - C.offset j : ℕ) : ℝ) * z - y)

noncomputable def carryNat (C : CarryShape) (j : Fin C.J) (z y : ℝ) : ℕ :=
  (C.carry j z y).toNat

noncomputable def cost (C : CarryShape) (z y : ℝ) : ℕ :=
  ∑ j : Fin C.J, C.weight j * C.carryNat j z y

theorem carry_eq_zero_or_one (C : CarryShape) (j : Fin C.J) (z y : ℝ) :
    C.carry j z y = 0 ∨ C.carry j z y = 1 :=
  floorCarry_zero_or_one _ _

theorem carryNat_eq_zero_or_one (C : CarryShape) (j : Fin C.J) (z y : ℝ) :
    C.carryNat j z y = 0 ∨ C.carryNat j z y = 1 := by
  rcases C.carry_eq_zero_or_one j z y with h | h
  · change (C.carry j z y).toNat = 0 ∨ (C.carry j z y).toNat = 1
    rw [h]
    simp
  · change (C.carry j z y).toNat = 0 ∨ (C.carry j z y).toNat = 1
    rw [h]
    simp

theorem cost_nonneg (C : CarryShape) (z y : ℝ) : 0 ≤ C.cost z y :=
  Nat.zero_le _

theorem carry_eq_expectedFormula (C : CarryShape) (j : Fin C.J)
    (z y : ℝ) :
    C.carry j z y =
      ⌊(((C.L - 2 * C.offset j : ℕ) : ℝ) * z)⌋ -
        ⌊y - (C.offset j : ℝ) * z⌋ -
        ⌊(((C.L - C.offset j : ℕ) : ℝ) * z) - y⌋ := by
  have h2 : 2 * C.offset j ≤ C.L := (C.twoOffset_lt j).le
  have ht : C.offset j ≤ C.L := by omega
  have hsub : C.L - 2 * C.offset j = (C.L - C.offset j) - C.offset j := by
    omega
  have hcast : ((C.L - 2 * C.offset j : ℕ) : ℝ) =
      ((C.L - C.offset j : ℕ) : ℝ) - (C.offset j : ℝ) := by
    rw [hsub, Nat.cast_sub (by omega : C.offset j ≤ C.L - C.offset j)]
  have hsum :
      (y - (C.offset j : ℝ) * z) +
        (((C.L - C.offset j : ℕ) : ℝ) * z - y) =
          (((C.L - 2 * C.offset j : ℕ) : ℝ) * z) := by
    rw [hcast]
    ring
  simp only [carry, floorCarry]
  rw [hsum]

private theorem floorCarry_shift (x y : ℝ) (m n : ℤ) :
    floorCarry (x + m) (y + n) = floorCarry x y := by
  have hsum : (x + m) + (y + n) = (x + y + m) + n := by ring
  have hf1 : ⌊(x + y + m) + n⌋ = ⌊x + y⌋ + m + n := by
    rw [Int.floor_add_intCast, Int.floor_add_intCast]
  have hf2 : ⌊x + m⌋ = ⌊x⌋ + m := Int.floor_add_intCast x m
  have hf3 : ⌊y + n⌋ = ⌊y⌋ + n := Int.floor_add_intCast y n
  unfold floorCarry
  rw [hsum, hf1, hf2, hf3]
  omega

/-- Every layer is determined by the relative order of `y` and the two
fractional endpoints `frac(t*z)` and `frac((L-t)*z)`. -/
theorem carry_eq_boundaryIndicators (C : CarryShape) (j : Fin C.J)
    (z y : ℝ) :
    C.carry j z y =
      (if Int.fract y < Int.fract ((C.offset j : ℕ) * z) then 1 else 0) +
      (if Int.fract (((C.L - C.offset j : ℕ) : ℝ) * z) < Int.fract y
        then 1 else 0) -
      (if Int.fract (((C.L - C.offset j : ℕ) : ℝ) * z) <
          Int.fract ((C.offset j : ℕ) * z) then 1 else 0) := by
  let α := Int.fract ((C.offset j : ℕ) * z)
  let β := Int.fract (((C.L - C.offset j : ℕ) : ℝ) * z)
  let γ := Int.fract y
  have hx : y - (C.offset j : ℝ) * z =
      (γ - α) + ((⌊y⌋ - ⌊(C.offset j : ℕ) * z⌋ : ℤ) : ℝ) := by
    calc
      y - (C.offset j : ℝ) * z =
          ((⌊y⌋ : ℝ) + γ) - ((⌊(C.offset j : ℕ) * z⌋ : ℝ) + α) := by
            rw [Int.floor_add_fract y,
              Int.floor_add_fract ((C.offset j : ℕ) * z)]
      _ = (γ - α) + ((⌊y⌋ - ⌊(C.offset j : ℕ) * z⌋ : ℤ) : ℝ) := by
            push_cast
            ring
  have hy : ((C.L - C.offset j : ℕ) : ℝ) * z - y =
      (β - γ) + ((⌊((C.L - C.offset j : ℕ) : ℝ) * z⌋ - ⌊y⌋ : ℤ) : ℝ) := by
    calc
      ((C.L - C.offset j : ℕ) : ℝ) * z - y =
          ((⌊((C.L - C.offset j : ℕ) : ℝ) * z⌋ : ℝ) + β) -
            ((⌊y⌋ : ℝ) + γ) := by
              rw [Int.floor_add_fract (((C.L - C.offset j : ℕ) : ℝ) * z),
                Int.floor_add_fract y]
      _ = (β - γ) +
          ((⌊((C.L - C.offset j : ℕ) : ℝ) * z⌋ - ⌊y⌋ : ℤ) : ℝ) := by
            push_cast
            ring
  have hshift := floorCarry_shift (γ - α) (β - γ)
    (⌊y⌋ - ⌊(C.offset j : ℕ) * z⌋)
    (⌊((C.L - C.offset j : ℕ) : ℝ) * z⌋ - ⌊y⌋)
  rw [carry, hx, hy]
  change floorCarry ((γ - α) + _) ((β - γ) + _) = _
  rw [hshift]
  exact floorCarry_unitDifference α γ β
    (Int.fract_nonneg _) (Int.fract_lt_one _)
    (Int.fract_nonneg _) (Int.fract_lt_one _)
    (Int.fract_nonneg _) (Int.fract_lt_one _)

theorem carry_add_int_z (C : CarryShape) (j : Fin C.J) (z y : ℝ) (k : ℤ) :
    C.carry j (z + k) y = C.carry j z y := by
  have hx : y - (C.offset j : ℝ) * (z + k) =
      (y - (C.offset j : ℝ) * z) + (-(C.offset j : ℤ) * k : ℝ) := by
    push_cast
    ring
  have hy : ((C.L - C.offset j : ℕ) : ℝ) * (z + k) - y =
      (((C.L - C.offset j : ℕ) : ℝ) * z - y) +
        (((C.L - C.offset j : ℕ) : ℤ) * k : ℝ) := by
    push_cast
    ring
  simp only [carry]
  rw [hx, hy]
  convert floorCarry_shift (y - (C.offset j : ℝ) * z)
    (((C.L - C.offset j : ℕ) : ℝ) * z - y)
    (-(C.offset j : ℤ) * k) (((C.L - C.offset j : ℕ) : ℤ) * k) using 1 <;>
      push_cast <;> ring

theorem carry_add_int_y (C : CarryShape) (j : Fin C.J) (z y : ℝ) (k : ℤ) :
    C.carry j z (y + k) = C.carry j z y := by
  have hx : y + k - (C.offset j : ℝ) * z =
      (y - (C.offset j : ℝ) * z) + k := by ring
  have hy : ((C.L - C.offset j : ℕ) : ℝ) * z - (y + k) =
      (((C.L - C.offset j : ℕ) : ℝ) * z - y) - k := by ring
  simp only [carry]
  rw [hx, hy]
  convert floorCarry_shift (y - (C.offset j : ℝ) * z)
    (((C.L - C.offset j : ℕ) : ℝ) * z - y) k (-k) using 1 <;>
      simp [sub_eq_add_neg]

theorem cost_add_int_z (C : CarryShape) (z y : ℝ) (k : ℤ) :
    C.cost (z + k) y = C.cost z y := by
  unfold cost
  apply Finset.sum_congr rfl
  intro j hj
  simp [carryNat, C.carry_add_int_z]

theorem cost_add_int_y (C : CarryShape) (z y : ℝ) (k : ℤ) :
    C.cost z (y + k) = C.cost z y := by
  unfold cost
  apply Finset.sum_congr rfl
  intro j hj
  simp [carryNat, C.carry_add_int_y]

/-- Uniformly scaling every layer weight scales the cost exactly. -/
def scaleWeights (C : CarryShape) (s : ℕ) : CarryShape :=
  { C with weight := fun j => s * C.weight j }

theorem cost_scaleWeights (C : CarryShape) (s : ℕ) (z y : ℝ) :
    (C.scaleWeights s).cost z y = s * C.cost z y := by
  unfold scaleWeights cost
  change Finset.univ.sum (fun j : Fin C.J =>
      (s * C.weight j) * C.carryNat j z y) =
    s * Finset.univ.sum (fun j : Fin C.J => C.weight j * C.carryNat j z y)
  rw [Finset.mul_sum Finset.univ
    (fun j : Fin C.J => C.weight j * C.carryNat j z y) s]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem cost_scaleWeights_ge (C : CarryShape) (s v : ℕ) (z y : ℝ)
    (h : v ≤ C.cost z y) :
    s * v ≤ (C.scaleWeights s).cost z y := by
  rw [C.cost_scaleWeights]
  exact Nat.mul_le_mul_left s h

/-- Real-valued cost can be studied on the unit square. -/
theorem cost_fract_z (C : CarryShape) (z y : ℝ) :
    C.cost (Int.fract z) y = C.cost z y := by
  have hz : z = Int.fract z + (⌊z⌋ : ℝ) := by
    have h := Int.floor_add_fract z
    linarith
  calc
    C.cost (Int.fract z) y = C.cost (Int.fract z + (⌊z⌋ : ℝ)) y :=
      (C.cost_add_int_z (Int.fract z) y ⌊z⌋).symm
    _ = C.cost z y := by rw [← hz]

/-- Real-valued cost can be studied on the unit square. -/
theorem cost_fract_y (C : CarryShape) (z y : ℝ) :
    C.cost z (Int.fract y) = C.cost z y := by
  have hy : y = Int.fract y + (⌊y⌋ : ℝ) := by
    have h := Int.floor_add_fract y
    linarith
  calc
    C.cost z (Int.fract y) = C.cost z (Int.fract y + (⌊y⌋ : ℝ)) :=
      (C.cost_add_int_y z (Int.fract y) ⌊y⌋).symm
    _ = C.cost z y := by rw [← hy]

end CarryShape

/-! The transparent two-layer configuration from the arithmetic notes. -/
abbrev twoLayerShape : CarryShape where
  L := 14
  J := 2
  offset := fun j => j.val
  weight := fun _ => 1
  twoOffset_lt := by
    intro j
    have hj := j.isLt
    simp
    omega

@[simp] theorem twoLayerShape_weight (j : Fin twoLayerShape.J) :
    twoLayerShape.weight j = 1 := rfl

/-- On the target open interval the two-layer continuous cost is at least
one for every real `y`. -/
theorem twoLayer_cost_ge_one {z y : ℝ}
    (hzlo : 1 / 14 < z) (hzhi : z < 1 / 13) :
    twoLayerShape.cost z y ≥ 1 := by
  let γ := Int.fract y
  have hz0 : 0 < z := by norm_num at hzlo; linarith
  have hzlt1 : z < 1 := by norm_num; linarith
  have h14lo : 1 < 14 * z := by nlinarith
  have h14hi : 14 * z < 2 := by nlinarith
  have h13lo : 0 < 13 * z := by nlinarith
  have h13hi : 13 * z < 1 := by nlinarith
  have hfrac14 : Int.fract (14 * z) = 14 * z - 1 := by
    have hf : ⌊14 * z⌋ = (1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast le_of_lt h14lo
      · exact_mod_cast h14hi
    unfold Int.fract
    rw [hf]
    norm_num
  have hfracz : Int.fract z = z := Int.fract_eq_self.mpr ⟨by linarith, hzlt1⟩
  have hfrac13 : Int.fract (13 * z) = 13 * z :=
    Int.fract_eq_self.mpr ⟨le_of_lt h13lo, h13hi⟩
  have hγ0 : 0 ≤ γ := Int.fract_nonneg y
  have hγ1 : γ < 1 := Int.fract_lt_one y
  have hγ : Int.fract y = γ := rfl
  have h14not : ¬14 * z < 1 := by linarith
  have hcarry0 : twoLayerShape.carry ⟨0, by decide⟩ z y =
      (if 14 * z - 1 < γ then 1 else 0) := by
    rw [twoLayerShape.carry_eq_boundaryIndicators]
    simp [twoLayerShape, hγ, hfrac14, hγ0, h14not]
  have hcarry1 : twoLayerShape.carry ⟨1, by decide⟩ z y =
      (if γ < z then 1 else 0) + (if 13 * z < γ then 1 else 0) := by
    rw [twoLayerShape.carry_eq_boundaryIndicators]
    simp [twoLayerShape, γ, hfracz, hfrac13, hz0]
  have hnat0 : twoLayerShape.carryNat ⟨0, by decide⟩ z y =
      (if 14 * z - 1 < γ then 1 else 0) := by
    unfold CarryShape.carryNat
    rw [hcarry0]
    split_ifs <;> simp
  have hnat1 : twoLayerShape.carryNat ⟨1, by decide⟩ z y =
      (if γ < z then 1 else 0) + (if 13 * z < γ then 1 else 0) := by
    unfold CarryShape.carryNat
    rw [hcarry1]
    by_cases h₁ : γ < z
    · have h₂ : ¬ 13 * z < γ := by nlinarith
      simp [h₁, h₂]
    · by_cases h₂ : 13 * z < γ <;> simp [h₁, h₂]
  have hsum : (if 14 * z - 1 < γ then 1 else 0) +
      ((if γ < z then 1 else 0) + (if 13 * z < γ then 1 else 0)) ≥ 1 := by
    by_cases hcut : 14 * z - 1 < γ
    · simp [hcut]
    · have hγle : γ ≤ 14 * z - 1 := le_of_not_gt hcut
      have hgap : 14 * z - 1 < z := by nlinarith
      have hγlt : γ < z := lt_of_le_of_lt hγle hgap
      simp [hcut, hγlt]
  unfold CarryShape.cost
  change (∑ j : Fin 2, twoLayerShape.weight j *
    twoLayerShape.carryNat j z y) ≥ 1
  rw [Fin.sum_univ_two]
  simp only [twoLayerShape] at hnat0 hnat1 ⊢
  have hfin0 : (0 : Fin 2) = ⟨0, by decide⟩ := Fin.ext rfl
  have hfin1 : (1 : Fin 2) = ⟨1, by decide⟩ := Fin.ext rfl
  rw [hfin0, hfin1, hnat0, hnat1]
  simpa only [one_mul] using hsum

/-- The same two-layer argument applies on every positive fine cell. The
integer `k` records the adjacent values of `floor (14*z)` and `floor (13*z)`;
the two lower endpoints enforce the ordering of the moving y-breakpoints. -/
theorem twoLayer_cost_ge_one_of_fineCell {k : ℕ} {z y : ℝ}
    (hklo : 1 ≤ k) (hkhi : k ≤ 12)
    (hzlo : max ((k : ℝ) / 14) (((k : ℝ) - 1) / 12) < z)
    (hzhi : z < (k : ℝ) / 13) :
    twoLayerShape.cost z y ≥ 1 := by
  have hkloR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hklo
  have hkhiR : (k : ℝ) ≤ 12 := by exact_mod_cast hkhi
  have hklt13 : (k : ℝ) < 13 := by linarith
  have hlow14 : (k : ℝ) / 14 < z :=
    lt_of_le_of_lt (le_max_left _ _) hzlo
  have hlow12 : ((k : ℝ) - 1) / 12 < z :=
    lt_of_le_of_lt (le_max_right _ _) hzlo
  have hzpos : 0 < z := by nlinarith
  have hzlt1 : z < 1 := by nlinarith
  have h14lo : (k : ℝ) < 14 * z := by nlinarith
  have h14lo' : (k : ℝ) ≤ 14 * z := le_of_lt h14lo
  have h14hi : 14 * z < (k : ℝ) + 1 := by nlinarith
  have h12lo : (k : ℝ) - 1 < 12 * z := by nlinarith
  have h13lo : (k : ℝ) - 1 ≤ 13 * z := by nlinarith
  have h13hi : 13 * z < (k : ℝ) := by nlinarith
  have hfloor14 : ⌊14 * z⌋ = (k : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast le_of_lt h14lo
    · exact_mod_cast h14hi
  have hfloor13 : ⌊13 * z⌋ = (k : ℤ) - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast h13lo
    · have h13hi' : 13 * z < ((k : ℝ) - 1) + 1 := by linarith
      exact_mod_cast h13hi'
  have hfrac14 : Int.fract (14 * z) = 14 * z - (k : ℝ) := by
    unfold Int.fract
    rw [hfloor14]
    push_cast
    ring
  have hfracz : Int.fract z = z :=
    Int.fract_eq_self.mpr ⟨le_of_lt hzpos, hzlt1⟩
  have hfrac13 : Int.fract (13 * z) = 13 * z - ((k : ℝ) - 1) := by
    unfold Int.fract
    rw [hfloor13]
    push_cast
    ring
  let γ := Int.fract y
  have hγ0 : 0 ≤ γ := Int.fract_nonneg y
  have hγ1 : γ < 1 := Int.fract_lt_one y
  have hδltα : 14 * z - (k : ℝ) < z := by nlinarith
  have hδ0 : 0 ≤ 14 * z - (k : ℝ) := by nlinarith
  have hαleβ : z ≤ 13 * z - ((k : ℝ) - 1) := by nlinarith
  have hγneg : ¬ Int.fract y < 0 := not_lt.mpr (Int.fract_nonneg y)
  have hcarry0 : twoLayerShape.carry ⟨0, by decide⟩ z y =
      (if 14 * z - (k : ℝ) < γ then 1 else 0) := by
    rw [twoLayerShape.carry_eq_boundaryIndicators]
    simp [twoLayerShape, γ, hfrac14, hγneg, h14lo']
  have hcarry1 : twoLayerShape.carry ⟨1, by decide⟩ z y =
      (if γ < z then 1 else 0) +
        (if 13 * z - ((k : ℝ) - 1) < γ then 1 else 0) := by
    rw [twoLayerShape.carry_eq_boundaryIndicators]
    simp [twoLayerShape, γ, hfracz, hfrac13, hαleβ]
  have hnat0 : twoLayerShape.carryNat ⟨0, by decide⟩ z y =
      (if 14 * z - (k : ℝ) < γ then 1 else 0) := by
    unfold CarryShape.carryNat
    rw [hcarry0]
    split_ifs <;> simp
  have hnat1 : twoLayerShape.carryNat ⟨1, by decide⟩ z y =
      (if γ < z then 1 else 0) +
        (if 13 * z - ((k : ℝ) - 1) < γ then 1 else 0) := by
    unfold CarryShape.carryNat
    rw [hcarry1]
    by_cases h₁ : γ < z
    · have h₂ : ¬ 13 * z - ((k : ℝ) - 1) < γ := by linarith
      simp [h₁, h₂]
    · by_cases h₂ : 13 * z - ((k : ℝ) - 1) < γ <;> simp [h₁, h₂]
  have hsum : (if 14 * z - (k : ℝ) < γ then 1 else 0) +
      ((if γ < z then 1 else 0) +
        (if 13 * z - ((k : ℝ) - 1) < γ then 1 else 0)) ≥ 1 := by
    by_cases hcut : 14 * z - (k : ℝ) < γ
    · simp [hcut]
    · have hγle : γ ≤ 14 * z - (k : ℝ) := le_of_not_gt hcut
      have hγlt : γ < z := lt_of_le_of_lt hγle hδltα
      simp [hcut, hγlt]
  unfold CarryShape.cost
  change (∑ j : Fin 2, twoLayerShape.weight j *
    twoLayerShape.carryNat j z y) ≥ 1
  rw [Fin.sum_univ_two]
  simp only [twoLayerShape] at hnat0 hnat1 ⊢
  have hfin0 : (0 : Fin 2) = ⟨0, by decide⟩ := Fin.ext rfl
  have hfin1 : (1 : Fin 2) = ⟨1, by decide⟩ := Fin.ext rfl
  rw [hfin0, hfin1, hnat0, hnat1]
  simpa only [one_mul] using hsum

/-- The lower endpoint of the k-th positive two-layer fine cell, k=1,...,12. -/
noncomputable def twoLayerFineCellLower (k : Fin 12) : ℝ :=
  max (((k.val + 1 : ℕ) : ℝ) / 14) ((k.val : ℝ) / 12)

/-- The upper endpoint of the k-th positive two-layer fine cell. -/
noncomputable def twoLayerFineCellUpper (k : Fin 12) : ℝ :=
  ((k.val + 1 : ℕ) : ℝ) / 13

/-- All twelve positive fine cells for the transparent two-layer shape. -/
noncomputable def twoLayerCompleteSparseBound (z : ℝ) : ℕ :=
  if ∃ k : Fin 12,
      twoLayerFineCellLower k < Int.fract z ∧
        Int.fract z < twoLayerFineCellUpper k then 1 else 0

theorem twoLayerCompleteSparseBound_le_cost (z y : ℝ) :
    twoLayerCompleteSparseBound z ≤ twoLayerShape.cost z y := by
  classical
  by_cases h : ∃ k : Fin 12,
      twoLayerFineCellLower k < Int.fract z ∧
        Int.fract z < twoLayerFineCellUpper k
  · rcases h with ⟨k, hzlo, hzhi⟩
    have hklo : 1 ≤ k.val + 1 := by omega
    have hkhi : k.val + 1 ≤ 12 := by omega
    have hzlo1 : (((k.val + 1 : ℕ) : ℝ) / 14) < Int.fract z := by
      have h := hzlo
      change max _ _ < _ at h
      exact (max_lt_iff.mp h).1
    have hzlo2 : ((k.val : ℝ) / 12) < Int.fract z := by
      have h := hzlo
      change max _ _ < _ at h
      exact (max_lt_iff.mp h).2
    have hcast : (((k.val + 1 : ℕ) : ℝ) - 1) / 12 =
        (k.val : ℝ) / 12 := by push_cast; ring
    have hzlo' : max (((k.val + 1 : ℕ) : ℝ) / 14)
        ((((k.val + 1 : ℕ) : ℝ) - 1) / 12) < Int.fract z := by
      rw [max_lt_iff]
      constructor
      · exact hzlo1
      · rw [hcast]
        exact hzlo2
    have hcell := twoLayer_cost_ge_one_of_fineCell (z := Int.fract z) (y := y)
      hklo hkhi hzlo' hzhi
    have hex : ∃ k' : Fin 12,
        twoLayerFineCellLower k' < Int.fract z ∧
          Int.fract z < twoLayerFineCellUpper k' := ⟨k, hzlo, hzhi⟩
    rw [twoLayerCompleteSparseBound, if_pos hex]
    rw [← CarryShape.cost_fract_z twoLayerShape z y]
    exact hcell
  · simp [twoLayerCompleteSparseBound, h]

theorem twoLayerFineCellEndpoints_table :
    (∀ k : Fin 7,
        twoLayerFineCellLower ⟨k.val, by omega⟩ =
          ((k.val + 1 : ℕ) : ℝ) / 14) ∧
    (∀ k : Fin 5,
        twoLayerFineCellLower ⟨k.val + 7, by omega⟩ =
          ((k.val + 7 : ℕ) : ℝ) / 12) := by
  constructor <;> intro k <;> fin_cases k <;>
    norm_num [twoLayerFineCellLower]

theorem twoLayerCompleteSparseBound_at_three_over_fortyOne :
    twoLayerCompleteSparseBound (3 / 41) = 1 := by
  have hcell : twoLayerFineCellLower (⟨0, by omega⟩ : Fin 12) <
      Int.fract (3 / 41) ∧
      Int.fract (3 / 41) <
        twoLayerFineCellUpper (⟨0, by omega⟩ : Fin 12) := by
    norm_num [twoLayerFineCellLower, twoLayerFineCellUpper, Int.fract]
  have hex : ∃ k : Fin 12,
      twoLayerFineCellLower k < Int.fract (3 / 41) ∧
        Int.fract (3 / 41) < twoLayerFineCellUpper k :=
    ⟨⟨0, by omega⟩, hcell⟩
  simp [twoLayerCompleteSparseBound, hex]

/-- A sparse periodic lower-bound function: outside the certified cell it is
zero, so nonnegativity supplies the bound there. -/
noncomputable def twoLayerSparseBound (z : ℝ) : ℕ :=
  if 1 / 14 < Int.fract z ∧ Int.fract z < 1 / 13 then 1 else 0

theorem twoLayerSparseBound_le_cost (z y : ℝ) :
    twoLayerSparseBound z ≤ twoLayerShape.cost z y := by
  by_cases h : 1 / 14 < Int.fract z ∧ Int.fract z < 1 / 13
  · have hcell := twoLayer_cost_ge_one h.1 h.2 (y := y)
    rw [twoLayerSparseBound, if_pos h]
    rw [← CarryShape.cost_fract_z twoLayerShape z y]
    exact hcell
  · rw [twoLayerSparseBound, if_neg h]
    exact Nat.zero_le _

theorem twoLayerSparseBound_at_three_over_fortyOne :
    twoLayerSparseBound (3 / 41) = 1 := by
  norm_num [twoLayerSparseBound, Int.fract]

end OddPiPowers

end
