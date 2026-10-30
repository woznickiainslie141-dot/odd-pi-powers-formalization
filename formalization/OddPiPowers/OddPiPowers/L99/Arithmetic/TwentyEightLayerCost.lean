module

public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellSoundness

@[expose] public section

namespace OddPiPowers.L99

open scoped BigOperators

private theorem pointIndicator_eq_layer (ra rb rq : ℕ) :
    (if rq < ra then 1 else 0) + (if rb < rq then 1 else 0) -
        (if rb < ra then 1 else 0) =
      if rb < ra then (if rb < rq ∧ rq < ra then 1 else 0)
      else if rq < ra ∨ rb < rq then 1 else 0 := by
  by_cases hba : rb < ra <;> by_cases hqa : rq < ra <;> by_cases hbq : rb < rq <;>
    simp [hba, hqa, hbq] <;> omega

private theorem gapIndicator_eq_layer (ra rb k : ℕ) :
    (if k < ra then 1 else 0) + (if rb ≤ k then 1 else 0) -
        (if rb < ra then 1 else 0) =
      if rb < ra then (if rb ≤ k ∧ k < ra then 1 else 0)
      else if k < ra ∨ rb ≤ k then 1 else 0 := by
  by_cases hba : rb < ra <;> by_cases hka : k < ra <;> by_cases hbk : rb ≤ k <;>
    simp [hba, hka, hbk] <;> omega

private theorem carryNat_boundaryIndicators (C : CarryShape) (j : Fin C.J)
    (z y : ℝ) :
    C.carryNat j z y =
      (if Int.fract y < Int.fract ((C.offset j : ℕ) * z) then 1 else 0) +
      (if Int.fract (((C.L - C.offset j : ℕ) : ℝ) * z) < Int.fract y
        then 1 else 0) -
      (if Int.fract (((C.L - C.offset j : ℕ) : ℝ) * z) <
          Int.fract ((C.offset j : ℕ) * z) then 1 else 0) := by
  let a : ℕ := if Int.fract y < Int.fract ((C.offset j : ℕ) * z) then 1 else 0
  let b : ℕ := if Int.fract (((C.L - C.offset j : ℕ) : ℝ) * z) < Int.fract y
    then 1 else 0
  let d : ℕ := if Int.fract (((C.L - C.offset j : ℕ) : ℝ) * z) <
      Int.fract ((C.offset j : ℕ) * z) then 1 else 0
  have hcarry : C.carry j z y = (a : ℤ) + (b : ℤ) - (d : ℤ) := by
    rw [C.carry_eq_boundaryIndicators]
    simp [a, b, d]
  have hnonneg : 0 ≤ (a : ℤ) + (b : ℤ) - (d : ℤ) := by
    rw [← hcarry]
    rcases C.carry_eq_zero_or_one j z y with h | h <;> simp [h]
  have hsub : d ≤ a + b := by omega
  have hcast : (a : ℤ) + (b : ℤ) - (d : ℤ) = ((a + b - d : ℕ) : ℤ) := by
    norm_cast
  change (C.carry j z y).toNat = a + b - d
  rw [hcarry, hcast]
  simp

private theorem twentyEightCarryNat_boundaryIndicators (j : Fin 28) (z y : ℝ) :
    twentyEightLayerShape.carryNat j z y =
      (if Int.fract y < twentyEightEndpointReal (twentyEightAlpha j) z then 1 else 0) +
      (if twentyEightEndpointReal (twentyEightBeta j) z < Int.fract y then 1 else 0) -
      (if twentyEightEndpointReal (twentyEightBeta j) z < twentyEightEndpointReal (twentyEightAlpha j) z
        then 1 else 0) := by
  simp only [twentyEightLayerShape]
  rw [carryNat_boundaryIndicators]
  have ha : Int.fract ((twentyEightLayerShape.offset j : ℕ) * z) =
      twentyEightEndpointReal (twentyEightAlpha j) z := by
    unfold twentyEightEndpointReal
    change Int.fract ((j.val : ℝ) * z) =
      Int.fract ((twentyEightEndpointSlope (twentyEightAlpha j) : ℝ) * z)
    rw [twentyEightEndpointSlope_alpha]
  have hb : Int.fract (((twentyEightLayerShape.L - twentyEightLayerShape.offset j : ℕ) : ℝ) * z) =
      twentyEightEndpointReal (twentyEightBeta j) z := by
    unfold twentyEightEndpointReal
    change Int.fract (((99 - j.val : ℕ) : ℝ) * z) =
      Int.fract ((twentyEightEndpointSlope (twentyEightBeta j) : ℝ) * z)
    rw [twentyEightEndpointSlope_beta]
  simp only [twentyEightLayerShape] at ha hb
  rw [ha, hb]

private theorem twentyEightLayer_cost_eq_pointCost (c : TwentyEightCellCertificate)
    (hc : c.Valid) {z y : ℝ}
    (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (q : TwentyEightEndpoint)
    (hyq : Int.fract y = twentyEightEndpointReal q z) :
    twentyEightLayerShape.cost z (Int.fract y) = twentyEightPointCost c.rankCode q := by
  classical
  simp only [CarryShape.cost, twentyEightLayerShape, twentyEightPointCost, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro j hj
  congr 1
  have hcarry := twentyEightCarryNat_boundaryIndicators j z (Int.fract y)
  simp only [twentyEightLayerShape] at hcarry
  rw [hcarry]
  have hya : Int.fract y < twentyEightEndpointReal (twentyEightAlpha j) z ↔
      (twentyEightRank c.rankCode q).val < (twentyEightRank c.rankCode (twentyEightAlpha j)).val := by
    rw [hyq]
    exact TwentyEightCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr q (twentyEightAlpha j)
  have hby : twentyEightEndpointReal (twentyEightBeta j) z < Int.fract y ↔
      (twentyEightRank c.rankCode (twentyEightBeta j)).val < (twentyEightRank c.rankCode q).val := by
    rw [hyq]
    exact TwentyEightCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr
      (twentyEightBeta j) q
  have hba : twentyEightEndpointReal (twentyEightBeta j) z <
      twentyEightEndpointReal (twentyEightAlpha j) z ↔
      (twentyEightRank c.rankCode (twentyEightBeta j)).val <
        (twentyEightRank c.rankCode (twentyEightAlpha j)).val :=
    TwentyEightCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr
      (twentyEightBeta j) (twentyEightAlpha j)
  simpa [twentyEightPointLayer, hya, hby, hba] using
    (pointIndicator_eq_layer
      (twentyEightRank c.rankCode (twentyEightAlpha j)).val
      (twentyEightRank c.rankCode (twentyEightBeta j)).val
      (twentyEightRank c.rankCode q).val)

private theorem twentyEightLayer_cost_eq_gapCost (c : TwentyEightCellCertificate)
    (hc : c.Valid) {z y : ℝ}
    (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (k : TwentyEightEndpoint)
    (hbelow : ∀ i : TwentyEightEndpoint,
      twentyEightEndpointReal i z < Int.fract y ↔
        (twentyEightRank c.rankCode i).val ≤ k.val)
    (habove : ∀ i : TwentyEightEndpoint,
      Int.fract y < twentyEightEndpointReal i z ↔
        k.val < (twentyEightRank c.rankCode i).val) :
    twentyEightLayerShape.cost z (Int.fract y) = twentyEightGapCost c.rankCode k := by
  classical
  simp only [CarryShape.cost, twentyEightLayerShape, twentyEightGapCost, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro j hj
  congr 1
  have hcarry := twentyEightCarryNat_boundaryIndicators j z (Int.fract y)
  simp only [twentyEightLayerShape] at hcarry
  rw [hcarry]
  have hya : Int.fract y < twentyEightEndpointReal (twentyEightAlpha j) z ↔
      k.val < (twentyEightRank c.rankCode (twentyEightAlpha j)).val :=
    habove (twentyEightAlpha j)
  have hby : twentyEightEndpointReal (twentyEightBeta j) z < Int.fract y ↔
      (twentyEightRank c.rankCode (twentyEightBeta j)).val ≤ k.val :=
    hbelow (twentyEightBeta j)
  have hba : twentyEightEndpointReal (twentyEightBeta j) z <
      twentyEightEndpointReal (twentyEightAlpha j) z ↔
      (twentyEightRank c.rankCode (twentyEightBeta j)).val <
        (twentyEightRank c.rankCode (twentyEightAlpha j)).val :=
    TwentyEightCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr
      (twentyEightBeta j) (twentyEightAlpha j)
  simpa [twentyEightGapLayer, hya, hby, hba] using
    (gapIndicator_eq_layer
      (twentyEightRank c.rankCode (twentyEightAlpha j)).val
      (twentyEightRank c.rankCode (twentyEightBeta j)).val k.val)

theorem twentyEightLayerCell_cost_ge_value (c : TwentyEightCellCertificate)
    (hc : c.Valid) {z y : ℝ}
    (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ)) :
    c.value ≤ twentyEightLayerShape.cost z y := by
  let γ := Int.fract y
  have hγ := Int.fract_nonneg y
  have hγ1 := Int.fract_lt_one y
  rw [← CarryShape.cost_fract_y twentyEightLayerShape z y]
  change c.value ≤ twentyEightLayerShape.cost z γ
  by_cases hpoint : ∃ q : TwentyEightEndpoint, γ = twentyEightEndpointReal q z
  · rcases hpoint with ⟨q, hq⟩
    have hpointCost := twentyEightLayer_cost_eq_pointCost c hc hzl hzr q (by
      simpa [γ] using hq)
    rw [hpointCost]
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hgapLower, hpointLower⟩
    exact hpointLower q
  · have hz0 : twentyEightEndpointReal (twentyEightAlpha ⟨0, by decide⟩) z = 0 := by
      simp [twentyEightEndpointReal, twentyEightAlpha, twentyEightEndpointSlope,
        twentyEightEndpointSlope_alpha, Int.fract]
    have hγpos : 0 < γ := by
      by_contra hn
      have hγeq : γ = 0 := by linarith
      exact hpoint ⟨twentyEightAlpha ⟨0, by decide⟩, by rw [hz0]; exact hγeq⟩
    let S : Finset TwentyEightEndpoint :=
      Finset.univ.filter (fun i => twentyEightEndpointReal i z < γ)
    let R : Finset ℕ := S.image (fun i => (twentyEightRank c.rankCode i).val)
    have hSne : S.Nonempty := by
      refine ⟨twentyEightAlpha ⟨0, by decide⟩, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hz0]
      exact hγpos
    have hRne : R.Nonempty := by
      rcases hSne with ⟨i, hi⟩
      exact ⟨(twentyEightRank c.rankCode i).val,
        Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    let rmax : ℕ := R.max' hRne
    have hrmax : rmax ∈ R := by
      exact Finset.max'_mem R hRne
    obtain ⟨q, hqS, hqr⟩ := Finset.mem_image.mp hrmax
    have hqBelow : twentyEightEndpointReal q z < γ := by simpa [S] using hqS
    have hinj : Function.Injective (twentyEightRank c.rankCode) := by
      rcases hc with ⟨_, _, _, _, _, hn, _, _, _, _, _, _⟩
      exact List.nodup_ofFn.mp hn
    have hbelow (i : TwentyEightEndpoint) :
        twentyEightEndpointReal i z < γ ↔ (twentyEightRank c.rankCode i).val ≤ rmax := by
      constructor
      · intro hi
        have hiS : i ∈ S := by simp [S, hi]
        have hiR : (twentyEightRank c.rankCode i).val ∈ R :=
          Finset.mem_image.mpr ⟨i, hiS, rfl⟩
        exact Finset.le_max' R _ hiR
      · intro hle
        by_cases heq : (twentyEightRank c.rankCode i).val = rmax
        · have hrank : twentyEightRank c.rankCode i = twentyEightRank c.rankCode q := by
            apply Fin.ext
            simpa [hqr] using heq
          have hiq : i = q := hinj hrank
          subst q
          simpa [S] using hqS
        · have hlt : (twentyEightRank c.rankCode i).val <
              (twentyEightRank c.rankCode q).val := by
            rw [hqr]
            omega
          have horder := TwentyEightCellCertificate.endpoint_lt_of_rank_lt
            hc hzl hzr hlt
          exact horder.trans hqBelow
    have habove (i : TwentyEightEndpoint) :
        γ < twentyEightEndpointReal i z ↔ rmax < (twentyEightRank c.rankCode i).val := by
      constructor
      · intro hγi
        by_contra hn
        have hle : (twentyEightRank c.rankCode i).val ≤ rmax := Nat.le_of_not_gt hn
        exact lt_asymm hγi ((hbelow i).2 hle)
      · intro hri
        have hnot : ¬ twentyEightEndpointReal i z < γ := by
          intro hei
          have hle := (hbelow i).1 hei
          omega
        rcases lt_trichotomy γ (twentyEightEndpointReal i z) with hlt | heq | hgt
        · exact hlt
        · exact False.elim (hpoint ⟨i, heq⟩)
        · exact False.elim (hnot hgt)
    have hk : rmax < 56 := by
      rw [← hqr]
      exact (twentyEightRank c.rankCode q).isLt
    let k : TwentyEightEndpoint := ⟨rmax, hk⟩
    have hcost := twentyEightLayer_cost_eq_gapCost c hc hzl hzr k
      (by simpa [γ, k] using hbelow) (by simpa [γ, k] using habove)
    rw [hcost]
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hgapLower, hpointLower⟩
    exact hgapLower k

end OddPiPowers.L99

end
