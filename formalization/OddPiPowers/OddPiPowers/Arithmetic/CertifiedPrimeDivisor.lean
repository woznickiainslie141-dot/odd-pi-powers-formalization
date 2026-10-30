module

public import OddPiPowers.Arithmetic.ContinuousCarry
public import OddPiPowers.Arithmetic.PrimeDivisorExample

@[expose] public section

namespace OddPiPowers

namespace ActualIntervals

private theorem floor_int_div_nat (p : ℕ) (x : ℤ) :
    ⌊(x : ℝ) / (p : ℝ)⌋ = x / (p : ℤ) := by
  exact floor_intCast_div_nat x p

private theorem floor_nat_div_nat (p x : ℕ) :
    ⌊(x : ℝ) / (p : ℝ)⌋ = (x : ℤ) / (p : ℤ) := by
  convert floor_int_div_nat p (x : ℤ) using 1 <;> norm_cast

private theorem int_div_nat_eq_floor (p : ℕ) (hp : 0 < p) (x : ℤ) :
    x / (p : ℤ) = ⌊(x : ℝ) / (p : ℝ)⌋ :=
  (floor_int_div_nat p x).symm

/-- One actual interval with left endpoint `t*N` has exactly the continuous
carry for offset `t` at `(N/p, ell/p)`. The signed integer differences are
preserved throughout, including when `ell` lies outside the interval. -/
theorem intervalCarry_eq_shape_of_left {M : ℕ} (P : ActualIntervals M)
    (C : CarryShape) (a : Fin M) (j : Fin C.J) (N p ell : ℕ)
    (hn : P.n = C.L * N)
    (hleft : P.left a = C.offset j * N)
    (hp : 0 < p) :
    P.intervalCarry a p ell = C.carry j (N / p) (ell / p) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2le : 2 * C.offset j ≤ C.L := (C.twoOffset_lt j).le
  have htle : C.offset j ≤ C.L := by omega
  have hlen : P.length a = (C.L - 2 * C.offset j) * N := by
    unfold ActualIntervals.length
    rw [hn, hleft]
    calc
      C.L * N - 2 * (C.offset j * N) = C.L * N -
          (2 * C.offset j) * N := by rw [← Nat.mul_assoc]
      _ = (C.L - 2 * C.offset j) * N := by
        rw [← Nat.mul_sub_right_distrib]
  have hright : P.right a = (C.L - C.offset j) * N := by
    unfold ActualIntervals.right
    rw [hn, hleft]
    rw [← Nat.mul_sub_right_distrib]
  rw [ActualIntervals.intervalCarry, C.carry_eq_expectedFormula]
  rw [← floor_intCast_div_nat (P.length a) p,
    ← floor_intCast_div_nat ((ell : ℤ) - (P.left a : ℤ)) p,
    ← floor_intCast_div_nat ((P.right a : ℤ) - (ell : ℤ)) p]
  have hfirst : ((P.length a : ℤ) : ℝ) / (p : ℝ) =
      ((C.L - 2 * C.offset j : ℕ) : ℝ) * ((N : ℝ) / (p : ℝ)) := by
    rw [hlen]
    have hsubCast : ((C.L - 2 * C.offset j : ℕ) : ℝ) =
        (C.L : ℝ) - 2 * (C.offset j : ℝ) := by
      rw [Nat.cast_sub h2le]
      push_cast
      ring
    push_cast
    rw [hsubCast]
    field_simp [hpR.ne']
    <;> ring
  have hsecond : (((ell : ℤ) - (P.left a : ℤ) : ℤ) : ℝ) / (p : ℝ) =
      (ell : ℝ) / (p : ℝ) - (C.offset j : ℝ) * ((N : ℝ) / (p : ℝ)) := by
    rw [hleft]
    push_cast
    field_simp [hpR.ne']
    <;> ring
  have hthird : (((P.right a : ℤ) - (ell : ℤ) : ℤ) : ℝ) / (p : ℝ) =
      ((C.L - C.offset j : ℕ) : ℝ) * ((N : ℝ) / (p : ℝ)) -
        (ell : ℝ) / (p : ℝ) := by
    rw [hright]
    have hsubCast : ((C.L - C.offset j : ℕ) : ℝ) =
        (C.L : ℝ) - (C.offset j : ℝ) := by
      rw [Nat.cast_sub htle]
    push_cast
    rw [hsubCast]
    field_simp [hpR.ne']
    <;> ring
  rw [hfirst, hsecond, hthird]

/-- A finite sigma equivalence makes the actual interval family a grouped
realization of one carry shape. Its fibers have exactly the prescribed
weights, and each group shares the corresponding scaled left endpoint. -/
structure ActualCarryGrouping {M : ℕ} (P : ActualIntervals M)
    (C : CarryShape) (N : ℕ) where
  indexEquiv : Fin M ≃ Σ j : Fin C.J, Fin (C.weight j)
  n_eq : P.n = C.L * N
  left_eq : ∀ a, P.left a = C.offset (indexEquiv a).1 * N

theorem ActualCarryGrouping.intervalCarry_eq_shape {M : ℕ}
    {P : ActualIntervals M} {C : CarryShape} {N : ℕ}
    (G : ActualCarryGrouping P C N) (a : Fin M) (p ell : ℕ)
    (hp : 0 < p) :
    P.intervalCarry a p ell =
      C.carry (G.indexEquiv a).1 (N / p) (ell / p) := by
  exact intervalCarry_eq_shape_of_left P C a (G.indexEquiv a).1 N p ell
    G.n_eq (G.left_eq a) hp

theorem ActualCarryGrouping.carryWeight_eq_cost {M : ℕ}
    {P : ActualIntervals M} {C : CarryShape} {N : ℕ}
    (G : ActualCarryGrouping P C N) (p ell : ℕ) (hp : 0 < p) :
    P.carryWeight p ell = C.cost (N / p) (ell / p) := by
  classical
  unfold ActualIntervals.carryWeight CarryShape.cost
  change (∑ a : Fin M, P.intervalCarryNat a p ell) =
    ∑ j : Fin C.J, C.weight j * C.carryNat j (N / p) (ell / p)
  calc
    (∑ a : Fin M, P.intervalCarryNat a p ell) =
        ∑ x : Σ j : Fin C.J, Fin (C.weight j),
          P.intervalCarryNat (G.indexEquiv.symm x) p ell := by
      exact Fintype.sum_equiv G.indexEquiv _ _ (by intro a; simp)
    _ = ∑ x : Σ j : Fin C.J, Fin (C.weight j),
          C.carryNat x.1 (N / p) (ell / p) := by
      apply Fintype.sum_congr
      intro x
      have hx := G.intervalCarry_eq_shape (G.indexEquiv.symm x) p ell hp
      simp only [ActualIntervals.intervalCarryNat, CarryShape.carryNat]
      rw [hx]
      simp
    _ = ∑ j : Fin C.J, ∑ k : Fin (C.weight j),
          C.carryNat j (N / p) (ell / p) := by
      rw [Fintype.sum_sigma]
    _ = ∑ j : Fin C.J, C.weight j * C.carryNat j (N / p) (ell / p) := by
      congr 1
      ext j
      simp [Finset.sum_const, Nat.mul_comm]

theorem ActualCarryGrouping.lowerBound_le_carryWeightMinimum {M : ℕ}
    {P : ActualIntervals M} {C : CarryShape} {N : ℕ}
    (G : ActualCarryGrouping P C N) (B : ℝ → ℕ)
    (hB : ∀ z y, B z ≤ C.cost z y) (p : ℕ) (hp : 0 < p) :
    B (N / p) ≤ P.carryWeightMinimum p := by
  unfold ActualIntervals.carryWeightMinimum
  apply Finset.le_inf'
  intro ell hell
  have hellBound : ell ≤ P.n := by
    have := Finset.mem_range.mp hell
    omega
  have hcost := hB (N / p) (ell / p)
  rw [← G.carryWeight_eq_cost p ell hp] at hcost
  exact hcost

noncomputable def ActualCarryGrouping.piCertificate {M : ℕ}
    {P : ActualIntervals M} {C : CarryShape} {N : ℕ}
    (G : ActualCarryGrouping P C N) (B : ℝ → ℕ) : ℕ :=
  ∏ p ∈ ActualIntervals.admissiblePrimeIndices P.n, p ^ B (N / p)

theorem ActualCarryGrouping.piCertificate_pos {M : ℕ}
    {P : ActualIntervals M} {C : CarryShape} {N : ℕ}
    (G : ActualCarryGrouping P C N) (B : ℝ → ℕ) :
    0 < G.piCertificate B := by
  classical
  unfold ActualCarryGrouping.piCertificate
  apply Finset.prod_pos
  intro p hp
  have hpprime := (Finset.mem_filter.mp hp).2.1
  exact pow_pos hpprime.pos _

theorem ActualCarryGrouping.piCertificate_dvd_actualDivisor {M : ℕ}
    {P : ActualIntervals M} {C : CarryShape} {N : ℕ}
    (G : ActualCarryGrouping P C N) (B : ℝ → ℕ)
    (hB : ∀ z y, B z ≤ C.cost z y) :
    G.piCertificate B ∣ P.actualAuxiliaryPrimeDivisor := by
  classical
  unfold ActualCarryGrouping.piCertificate ActualIntervals.actualAuxiliaryPrimeDivisor
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have hpprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hmin := G.lowerBound_le_carryWeightMinimum B hB p hpprime.pos
  exact pow_dvd_pow p hmin

theorem ActualCarryGrouping.piCertificate_dvd_integerCoefficients {M : ℕ}
    {P : ActualIntervals M} {C : CarryShape} {N : ℕ}
    (G : ActualCarryGrouping P C N) (B : ℝ → ℕ)
    (hB : ∀ z y, B z ≤ C.cost z y) (h j : Fin M) (k : ℕ) :
    (G.piCertificate B : ℤ) ∣ (actualAuxiliaryInt P h j).coeff k := by
  have hdiv := G.piCertificate_dvd_actualDivisor B hB
  have hcoeff := P.actualAuxiliaryPrimeDivisor_dvd_coeff (h := h) (j := j) k
  have hnat : G.piCertificate B ∣
      ((actualAuxiliaryInt P h j).coeff k).natAbs := dvd_trans hdiv hcoeff
  exact Int.natCast_dvd.mpr hnat

theorem example42_intervalCarry_eq_continuous (a : Fin 2) (p ell : ℕ)
    (hp : 0 < p) :
    exampleIntervals42.intervalCarry a p ell =
      twoLayerShape.carry a (3 / p) (ell / p) := by
  have hn : exampleIntervals42.n = twoLayerShape.L * 3 := by
    norm_num [exampleIntervals42, twoLayerShape]
  have hleft : exampleIntervals42.left a = twoLayerShape.offset a * 3 := by
    fin_cases a <;> norm_num [exampleIntervals42, twoLayerShape]
  exact intervalCarry_eq_shape_of_left exampleIntervals42 twoLayerShape a a
    3 p ell hn hleft hp

def example42CarryGrouping :
    ActualCarryGrouping exampleIntervals42 twoLayerShape 3 where
  indexEquiv :=
    { toFun := fun a => ⟨a, ⟨0, by simp [twoLayerShape]⟩⟩
      invFun := fun x => x.1
      left_inv := by intro a; rfl
      right_inv := by
        intro x
        rcases x with ⟨j, k⟩
        have hlt : k.val < 1 := by simpa [twoLayerShape] using k.isLt
        have hkval : k.val = 0 := by omega
        have hk : k = ⟨0, by simp [twoLayerShape]⟩ := Fin.ext hkval
        subst k
        rfl }
  n_eq := by norm_num [exampleIntervals42, twoLayerShape]
  left_eq := by
    intro a
    fin_cases a <;> norm_num [exampleIntervals42, twoLayerShape]

theorem example42_continuous_cost_eq (ell : Fin 43) :
    twoLayerShape.cost (3 / 41) (ell.val / 41) =
      exampleIntervals42.carryWeight 41 ell.val := by
  exact (ActualCarryGrouping.carryWeight_eq_cost example42CarryGrouping 41
    ell.val (by norm_num)).symm

noncomputable def example42PiCertificate : ℕ :=
  example42CarryGrouping.piCertificate twoLayerCompleteSparseBound

theorem example42PiCertificate_pos : 0 < example42PiCertificate :=
  example42CarryGrouping.piCertificate_pos twoLayerCompleteSparseBound

theorem example42PiCertificate_dvd_actualDivisor :
    example42PiCertificate ∣ exampleIntervals42.actualAuxiliaryPrimeDivisor :=
  example42CarryGrouping.piCertificate_dvd_actualDivisor
    twoLayerCompleteSparseBound twoLayerCompleteSparseBound_le_cost

theorem example42PiCertificate_dvd_integerCoefficients (h j : Fin 2) (k : ℕ) :
    (example42PiCertificate : ℤ) ∣
      (actualAuxiliaryInt exampleIntervals42 h j).coeff k :=
  example42CarryGrouping.piCertificate_dvd_integerCoefficients
    twoLayerCompleteSparseBound twoLayerCompleteSparseBound_le_cost h j k

theorem example42_41_dvd_PiCertificate : 41 ∣ example42PiCertificate := by
  have hmember : 41 ∈ ActualIntervals.admissiblePrimeIndices exampleIntervals42.n := by
    apply Finset.mem_filter.mpr
    constructor
    · simp [exampleIntervals42]
    · exact ⟨prime41, by norm_num [exampleIntervals42],
        by norm_num [exampleIntervals42]⟩
  have hpow : 41 ∣ 41 ^ twoLayerCompleteSparseBound (3 / 41) := by
    rw [twoLayerCompleteSparseBound_at_three_over_fortyOne]
    norm_num
  unfold example42PiCertificate ActualCarryGrouping.piCertificate
  apply dvd_trans hpow
  exact Finset.dvd_prod_of_mem _ hmember

theorem example42_carryWeight_ge_one_continuous (ell : Fin 43) :
    exampleIntervals42.carryWeight 41 ell.val ≥ 1 := by
  have hcontinuous : twoLayerCompleteSparseBound (3 / 41) ≤
      twoLayerShape.cost (3 / 41) (ell.val / 41) :=
    twoLayerCompleteSparseBound_le_cost (3 / 41) (ell.val / 41)
  rw [twoLayerCompleteSparseBound_at_three_over_fortyOne] at hcontinuous
  rw [example42_continuous_cost_eq] at hcontinuous
  exact hcontinuous

theorem example42_carryWeightMinimum_ge_one :
    exampleIntervals42.carryWeightMinimum 41 ≥ 1 := by
  unfold ActualIntervals.carryWeightMinimum
  apply Finset.le_inf'
  intro ell hell
  have helllt : ell < 43 := by
    simpa [exampleIntervals42] using Finset.mem_range.mp hell
  let e : Fin 43 := ⟨ell, helllt⟩
  have h := example42_carryWeight_ge_one_continuous e
  simpa [e] using h

theorem example42_41_dvd_actualAuxiliaryPrimeDivisor :
    41 ∣ exampleIntervals42.actualAuxiliaryPrimeDivisor :=
  dvd_trans example42_41_dvd_PiCertificate
    example42PiCertificate_dvd_actualDivisor

theorem example42_coeff_divisible_41_continuous (h j : Fin 2) (k : ℕ) :
    (41 : ℤ) ∣ (actualAuxiliaryInt exampleIntervals42 h j).coeff k := by
  have h41 : (41 : ℤ) ∣ (example42PiCertificate : ℤ) := by
    exact_mod_cast example42_41_dvd_PiCertificate
  exact dvd_trans h41 (example42PiCertificate_dvd_integerCoefficients h j k)

end ActualIntervals

end OddPiPowers

end
