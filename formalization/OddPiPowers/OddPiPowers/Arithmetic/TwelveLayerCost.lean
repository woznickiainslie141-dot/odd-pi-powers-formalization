module

public import OddPiPowers.Arithmetic.TwelveLayerCellSoundness

@[expose] public section

namespace OddPiPowers

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

private theorem twelveCarryNat_boundaryIndicators (j : Fin 12) (z y : ℝ) :
    twelveLayerShape.carryNat j z y =
      (if Int.fract y < twelveEndpointReal (twelveAlpha j) z then 1 else 0) +
      (if twelveEndpointReal (twelveBeta j) z < Int.fract y then 1 else 0) -
      (if twelveEndpointReal (twelveBeta j) z < twelveEndpointReal (twelveAlpha j) z
        then 1 else 0) := by
  simp only [twelveLayerShape]
  rw [carryNat_boundaryIndicators]
  have ha : Int.fract ((twelveLayerShape.offset j : ℕ) * z) =
      twelveEndpointReal (twelveAlpha j) z := by
    unfold twelveEndpointReal
    change Int.fract ((j.val : ℝ) * z) =
      Int.fract ((twelveEndpointSlope (twelveAlpha j) : ℝ) * z)
    rw [twelveEndpointSlope_alpha]
  have hb : Int.fract (((twelveLayerShape.L - twelveLayerShape.offset j : ℕ) : ℝ) * z) =
      twelveEndpointReal (twelveBeta j) z := by
    unfold twelveEndpointReal
    change Int.fract (((69 - j.val : ℕ) : ℝ) * z) =
      Int.fract ((twelveEndpointSlope (twelveBeta j) : ℝ) * z)
    rw [twelveEndpointSlope_beta]
  simp only [twelveLayerShape] at ha hb
  rw [ha, hb]

private theorem twelveLayer_cost_eq_pointCost (c : TwelveCellCertificate)
    (hc : c.Valid) {z y : ℝ}
    (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (q : TwelveEndpoint)
    (hyq : Int.fract y = twelveEndpointReal q z) :
    twelveLayerShape.cost z (Int.fract y) = twelvePointCost c.rankCode q := by
  classical
  simp only [CarryShape.cost, twelveLayerShape, twelvePointCost, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro j hj
  congr 1
  have hcarry := twelveCarryNat_boundaryIndicators j z (Int.fract y)
  simp only [twelveLayerShape] at hcarry
  rw [hcarry]
  have hya : Int.fract y < twelveEndpointReal (twelveAlpha j) z ↔
      (twelveRank c.rankCode q).val < (twelveRank c.rankCode (twelveAlpha j)).val := by
    rw [hyq]
    exact TwelveCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr q (twelveAlpha j)
  have hby : twelveEndpointReal (twelveBeta j) z < Int.fract y ↔
      (twelveRank c.rankCode (twelveBeta j)).val < (twelveRank c.rankCode q).val := by
    rw [hyq]
    exact TwelveCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr
      (twelveBeta j) q
  have hba : twelveEndpointReal (twelveBeta j) z <
      twelveEndpointReal (twelveAlpha j) z ↔
      (twelveRank c.rankCode (twelveBeta j)).val <
        (twelveRank c.rankCode (twelveAlpha j)).val :=
    TwelveCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr
      (twelveBeta j) (twelveAlpha j)
  simpa [twelvePointLayer, hya, hby, hba] using
    (pointIndicator_eq_layer
      (twelveRank c.rankCode (twelveAlpha j)).val
      (twelveRank c.rankCode (twelveBeta j)).val
      (twelveRank c.rankCode q).val)

private theorem twelveLayer_cost_eq_gapCost (c : TwelveCellCertificate)
    (hc : c.Valid) {z y : ℝ}
    (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (k : TwelveEndpoint)
    (hbelow : ∀ i : TwelveEndpoint,
      twelveEndpointReal i z < Int.fract y ↔
        (twelveRank c.rankCode i).val ≤ k.val)
    (habove : ∀ i : TwelveEndpoint,
      Int.fract y < twelveEndpointReal i z ↔
        k.val < (twelveRank c.rankCode i).val) :
    twelveLayerShape.cost z (Int.fract y) = twelveGapCost c.rankCode k := by
  classical
  simp only [CarryShape.cost, twelveLayerShape, twelveGapCost, List.sum_ofFn]
  refine Finset.sum_congr rfl ?_
  intro j hj
  congr 1
  have hcarry := twelveCarryNat_boundaryIndicators j z (Int.fract y)
  simp only [twelveLayerShape] at hcarry
  rw [hcarry]
  have hya : Int.fract y < twelveEndpointReal (twelveAlpha j) z ↔
      k.val < (twelveRank c.rankCode (twelveAlpha j)).val :=
    habove (twelveAlpha j)
  have hby : twelveEndpointReal (twelveBeta j) z < Int.fract y ↔
      (twelveRank c.rankCode (twelveBeta j)).val ≤ k.val :=
    hbelow (twelveBeta j)
  have hba : twelveEndpointReal (twelveBeta j) z <
      twelveEndpointReal (twelveAlpha j) z ↔
      (twelveRank c.rankCode (twelveBeta j)).val <
        (twelveRank c.rankCode (twelveAlpha j)).val :=
    TwelveCellCertificate.endpoint_lt_iff_rank_lt hc hzl hzr
      (twelveBeta j) (twelveAlpha j)
  simpa [twelveGapLayer, hya, hby, hba] using
    (gapIndicator_eq_layer
      (twelveRank c.rankCode (twelveAlpha j)).val
      (twelveRank c.rankCode (twelveBeta j)).val k.val)

theorem twelveLayerCell_cost_ge_value (c : TwelveCellCertificate)
    (hc : c.Valid) {z y : ℝ}
    (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ)) :
    c.value ≤ twelveLayerShape.cost z y := by
  let γ := Int.fract y
  have hγ := Int.fract_nonneg y
  have hγ1 := Int.fract_lt_one y
  rw [← CarryShape.cost_fract_y twelveLayerShape z y]
  change c.value ≤ twelveLayerShape.cost z γ
  by_cases hpoint : ∃ q : TwelveEndpoint, γ = twelveEndpointReal q z
  · rcases hpoint with ⟨q, hq⟩
    have hpointCost := twelveLayer_cost_eq_pointCost c hc hzl hzr q (by
      simpa [γ] using hq)
    rw [hpointCost]
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hgapLower, hpointLower⟩
    exact hpointLower q
  · have hz0 : twelveEndpointReal (twelveAlpha ⟨0, by decide⟩) z = 0 := by
      simp [twelveEndpointReal, twelveAlpha, twelveEndpointSlope,
        twelveEndpointSlope_alpha, Int.fract]
    have hγpos : 0 < γ := by
      by_contra hn
      have hγeq : γ = 0 := by linarith
      exact hpoint ⟨twelveAlpha ⟨0, by decide⟩, by rw [hz0]; exact hγeq⟩
    let S : Finset TwelveEndpoint :=
      Finset.univ.filter (fun i => twelveEndpointReal i z < γ)
    let R : Finset ℕ := S.image (fun i => (twelveRank c.rankCode i).val)
    have hSne : S.Nonempty := by
      refine ⟨twelveAlpha ⟨0, by decide⟩, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hz0]
      exact hγpos
    have hRne : R.Nonempty := by
      rcases hSne with ⟨i, hi⟩
      exact ⟨(twelveRank c.rankCode i).val,
        Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    let rmax : ℕ := R.max' hRne
    have hrmax : rmax ∈ R := by
      exact Finset.max'_mem R hRne
    obtain ⟨q, hqS, hqr⟩ := Finset.mem_image.mp hrmax
    have hqBelow : twelveEndpointReal q z < γ := by simpa [S] using hqS
    have hinj : Function.Injective (twelveRank c.rankCode) := by
      rcases hc with ⟨_, _, _, _, _, hn, _, _, _, _, _, _⟩
      exact List.nodup_ofFn.mp hn
    have hbelow (i : TwelveEndpoint) :
        twelveEndpointReal i z < γ ↔ (twelveRank c.rankCode i).val ≤ rmax := by
      constructor
      · intro hi
        have hiS : i ∈ S := by simp [S, hi]
        have hiR : (twelveRank c.rankCode i).val ∈ R :=
          Finset.mem_image.mpr ⟨i, hiS, rfl⟩
        exact Finset.le_max' R _ hiR
      · intro hle
        by_cases heq : (twelveRank c.rankCode i).val = rmax
        · have hrank : twelveRank c.rankCode i = twelveRank c.rankCode q := by
            apply Fin.ext
            simpa [hqr] using heq
          have hiq : i = q := hinj hrank
          subst q
          simpa [S] using hqS
        · have hlt : (twelveRank c.rankCode i).val <
              (twelveRank c.rankCode q).val := by
            rw [hqr]
            omega
          have horder := TwelveCellCertificate.endpoint_lt_of_rank_lt
            hc hzl hzr hlt
          exact horder.trans hqBelow
    have habove (i : TwelveEndpoint) :
        γ < twelveEndpointReal i z ↔ rmax < (twelveRank c.rankCode i).val := by
      constructor
      · intro hγi
        by_contra hn
        have hle : (twelveRank c.rankCode i).val ≤ rmax := Nat.le_of_not_gt hn
        exact lt_asymm hγi ((hbelow i).2 hle)
      · intro hri
        have hnot : ¬ twelveEndpointReal i z < γ := by
          intro hei
          have hle := (hbelow i).1 hei
          omega
        rcases lt_trichotomy γ (twelveEndpointReal i z) with hlt | heq | hgt
        · exact hlt
        · exact False.elim (hpoint ⟨i, heq⟩)
        · exact False.elim (hnot hgt)
    have hk : rmax < 24 := by
      rw [← hqr]
      exact (twelveRank c.rankCode q).isLt
    let k : TwelveEndpoint := ⟨rmax, hk⟩
    have hcost := twelveLayer_cost_eq_gapCost c hc hzl hzr k
      (by simpa [γ, k] using hbelow) (by simpa [γ, k] using habove)
    rw [hcost]
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hgapLower, hpointLower⟩
    exact hgapLower k

end OddPiPowers

end
