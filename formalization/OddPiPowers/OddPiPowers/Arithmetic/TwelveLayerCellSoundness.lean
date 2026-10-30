module
public import OddPiPowers.Arithmetic.TwelveLayerCellDefs
@[expose] public section
namespace OddPiPowers
open scoped BigOperators

private theorem twelveNat_affine_le (a b u v n d : ℕ) (hd : 0 < d)
    (h : a * n + v * d ≤ b * n + u * d) :
    (a : ℚ) * ((n : ℚ) / d) - u ≤ (b : ℚ) * ((n : ℚ) / d) - v := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hdne : (d : ℚ) ≠ 0 := ne_of_gt hdQ
  have hQ : (a : ℚ) * n + v * d ≤ (b : ℚ) * n + u * d := by
    exact_mod_cast h
  apply (mul_le_mul_iff_left₀ hdQ).mp
  simp only [sub_mul, mul_assoc, div_mul_cancel₀ _ hdne]
  linarith

theorem TwelveCellCertificate.unit_interval_of_valid {c : TwelveCellCertificate}
    (hc : c.Valid) : 0 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ 1 := by
  rcases hc with ⟨hld, hrd, hcross, hunit, _, _, _, _, _, _, _, _⟩
  have hldQ : (0 : ℚ) < c.leftDenominator := by exact_mod_cast hld
  have hrdQ : (0 : ℚ) < c.rightDenominator := by exact_mod_cast hrd
  refine ⟨by unfold left; positivity, ?_, ?_⟩
  · unfold left right
    rw [div_lt_div_iff₀ hldQ hrdQ]
    exact_mod_cast hcross
  · unfold right
    apply (div_le_one hrdQ).mpr
    exact_mod_cast hunit

theorem TwelveCellCertificate.floor_bounds_rat {c : TwelveCellCertificate}
    (hc : c.Valid) (i : TwelveEndpoint) :
    (twelveCellFloor c i : ℚ) ≤ (twelveEndpointSlope i : ℚ) * c.left ∧
      (twelveEndpointSlope i : ℚ) * c.right ≤ (twelveCellFloor c i : ℚ) + 1 := by
  rcases hc with ⟨hld, hrd, _, _, _, _, _, hf, _, _, _, _⟩
  have hldQ : (0 : ℚ) < c.leftDenominator := by exact_mod_cast hld
  have hrdQ : (0 : ℚ) < c.rightDenominator := by exact_mod_cast hrd
  constructor
  · change (twelveFloorDigit c.floorCode i : ℚ) ≤
      (twelveEndpointSlope i : ℚ) * ((c.leftNumerator : ℚ) / c.leftDenominator)
    rw [← mul_div_assoc, le_div_iff₀ hldQ]
    exact_mod_cast (hf i).1
  · change (twelveEndpointSlope i : ℚ) *
        ((c.rightNumerator : ℚ) / c.rightDenominator) ≤
      (twelveFloorDigit c.floorCode i : ℚ) + 1
    rw [← mul_div_assoc, div_le_iff₀ hrdQ]
    exact_mod_cast (hf i).2

theorem TwelveCellCertificate.adjacent_bounds_rat {c : TwelveCellCertificate}
    (hc : c.Valid) (k : Fin 23) :
    twelveEndpointAffine c (twelveOrderEndpoint c.orderCode k.castSucc) c.left ≤
        twelveEndpointAffine c (twelveOrderEndpoint c.orderCode k.succ) c.left ∧
    twelveEndpointAffine c (twelveOrderEndpoint c.orderCode k.castSucc) c.right ≤
        twelveEndpointAffine c (twelveOrderEndpoint c.orderCode k.succ) c.right := by
  rcases hc with ⟨hld, hrd, _, _, _, _, _, _, ha, _, _, _⟩
  constructor
  · simpa [twelveEndpointAffine, TwelveCellCertificate.left, twelveCellFloor] using
      twelveNat_affine_le
        (twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.castSucc))
        (twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.succ))
        (twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.castSucc))
        (twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.succ))
        c.leftNumerator c.leftDenominator hld (ha k).1
  · simpa [twelveEndpointAffine, TwelveCellCertificate.right, twelveCellFloor] using
      twelveNat_affine_le
        (twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.castSucc))
        (twelveEndpointSlope (twelveOrderEndpoint c.orderCode k.succ))
        (twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.castSucc))
        (twelveFloorDigit c.floorCode (twelveOrderEndpoint c.orderCode k.succ))
        c.rightNumerator c.rightDenominator hrd (ha k).2

private theorem monotone_fin24 {α : Type} [Preorder α] (f : Fin 24 → α)
    (hstep : ∀ k : Fin 23, f k.castSucc ≤ f k.succ) :
    ∀ a b : Fin 24, a.val ≤ b.val → f a ≤ f b := by
  intro a b hab
  let d := b.val - a.val
  have hd : b.val = a.val + d := by simp [d]; omega
  have aux : ∀ d (b : Fin 24), b.val = a.val + d → f a ≤ f b := by
    intro n
    induction n with
    | zero =>
      intro b hb
      have hEq : b = a := Fin.ext (by simpa using hb)
      subst b
      exact le_rfl
    | succ n ih =>
      intro b hb
      let mid : Fin 24 := ⟨a.val + n, by omega⟩
      have hmid : mid.val = a.val + n := by simp [mid]
      have hfirst := ih mid hmid
      have hlt : mid.val < 23 := by simp [mid]; omega
      let k : Fin 23 := ⟨mid.val, hlt⟩
      have hadj := hstep k
      have hleft : k.castSucc = mid := by apply Fin.ext; rfl
      have hright : k.succ = b := by apply Fin.ext; simp [k]; omega
      rw [hleft, hright] at hadj
      exact hfirst.trans hadj
  exact aux d b hd

namespace TwelveCellCertificate

theorem floor_eq_of_valid {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i : TwelveEndpoint) :
    Int.floor ((twelveEndpointSlope i : ℝ) * z) = twelveCellFloor c i := by
  have hfloor := floor_bounds_rat hc i
  have hs0 : (0 : ℝ) ≤ (twelveEndpointSlope i : ℝ) := by positivity
  have hqlo : (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope i : ℝ) * (c.left : ℝ) := by
    exact_mod_cast hfloor.1
  have hqhi : (twelveEndpointSlope i : ℝ) * (c.right : ℝ) ≤
      (twelveCellFloor c i : ℝ) + 1 := by
    exact_mod_cast hfloor.2
  have hlo : (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope i : ℝ) * z := by
    exact hqlo.trans (mul_le_mul_of_nonneg_left (le_of_lt hzl) hs0)
  have hhi : (twelveEndpointSlope i : ℝ) * z <
      (twelveCellFloor c i : ℝ) + 1 := by
    by_cases hs : twelveEndpointSlope i = 0
    · have hq : twelveCellFloor c i = 0 := by
        have hqlo' : (twelveCellFloor c i : ℝ) ≤ 0 := by
          simpa [hs] using hqlo
        have hqnn : (0 : ℝ) ≤ (twelveCellFloor c i : ℝ) := by
          have hI : (0 : ℤ) ≤ twelveCellFloor c i := by
            unfold twelveCellFloor
            exact Int.natCast_nonneg _
          exact_mod_cast hI
        exact_mod_cast le_antisymm hqlo' hqnn
      rw [hs, hq]
      norm_num
    · have hspos : (0 : ℝ) < (twelveEndpointSlope i : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hs
      have hmul : (twelveEndpointSlope i : ℝ) * z <
          (twelveEndpointSlope i : ℝ) * (c.right : ℝ) :=
        mul_lt_mul_of_pos_left hzr hspos
      exact hmul.trans_le hqhi
  apply Int.floor_eq_iff.mpr
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem endpoint_eq_affine_of_valid {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i : TwelveEndpoint) :
    twelveEndpointReal i z =
      (twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ) := by
  simp [twelveEndpointReal, Int.fract,
    floor_eq_of_valid hc hzl hzr i]

theorem endpoint_lt_of_rank_lt {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    {i j : TwelveEndpoint}
    (hij : (twelveRank c.rankCode i).val < (twelveRank c.rankCode j).val) :
    twelveEndpointReal i z < twelveEndpointReal j z := by
  have hei := endpoint_eq_affine_of_valid hc hzl hzr i
  have hej := endpoint_eq_affine_of_valid hc hzl hzr j
  have hadj := adjacent_bounds_rat hc
  rcases hc with ⟨_, _, _, _, _, hnodup, horderInv, _, _, _, _, _⟩
  have hinj : Function.Injective (twelveRank c.rankCode) := by
    exact List.nodup_ofFn.mp hnodup
  have hne : i ≠ j := by
    intro h
    subst j
    exact (Nat.lt_irrefl _ hij)
  have hsne : twelveEndpointSlope i ≠ twelveEndpointSlope j := by
    intro h
    exact hne (twelveEndpointSlope_injective h)
  have horderI : twelveOrderEndpoint c.orderCode (twelveRank c.rankCode i) = i :=
    hinj (horderInv (twelveRank c.rankCode i))
  have horderJ : twelveOrderEndpoint c.orderCode (twelveRank c.rankCode j) = j :=
    hinj (horderInv (twelveRank c.rankCode j))
  have hLeft := monotone_fin24
    (fun r => twelveEndpointAffine c (twelveOrderEndpoint c.orderCode r) c.left)
    (fun k => (hadj k).1) (twelveRank c.rankCode i) (twelveRank c.rankCode j)
    (Nat.le_of_lt hij)
  have hRight := monotone_fin24
    (fun r => twelveEndpointAffine c (twelveOrderEndpoint c.orderCode r) c.right)
    (fun k => (hadj k).2) (twelveRank c.rankCode i) (twelveRank c.rankCode j)
    (Nat.le_of_lt hij)
  rw [horderI, horderJ] at hLeft hRight
  have hLeftR : (twelveEndpointAffine c i c.left : ℝ) ≤
      (twelveEndpointAffine c j c.left : ℝ) := by exact_mod_cast hLeft
  have hRightR : (twelveEndpointAffine c i c.right : ℝ) ≤
      (twelveEndpointAffine c j c.right : ℝ) := by exact_mod_cast hRight
  have hLeftR' : (twelveEndpointSlope i : ℝ) * (c.left : ℝ) -
      (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope j : ℝ) * (c.left : ℝ) -
      (twelveCellFloor c j : ℝ) := by
    simpa [twelveEndpointAffine] using hLeftR
  have hRightR' : (twelveEndpointSlope i : ℝ) * (c.right : ℝ) -
      (twelveCellFloor c i : ℝ) ≤
      (twelveEndpointSlope j : ℝ) * (c.right : ℝ) -
      (twelveCellFloor c j : ℝ) := by
    simpa [twelveEndpointAffine] using hRightR
  rw [hei, hej]
  by_cases hs : twelveEndpointSlope i < twelveEndpointSlope j
  · have hsR : (twelveEndpointSlope i : ℝ) <
        (twelveEndpointSlope j : ℝ) := by exact_mod_cast hs
    have hpos : 0 < ((twelveEndpointSlope j : ℝ) -
        (twelveEndpointSlope i : ℝ)) * ((z - (c.left : ℝ))) :=
      mul_pos (sub_pos.mpr hsR) (sub_pos.mpr hzl)
    have hdiff :
        ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) <
        ((twelveEndpointSlope i : ℝ) * (c.left : ℝ) -
            (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * (c.left : ℝ) -
            (twelveCellFloor c j : ℝ)) := by
      have heq :
          ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) =
            (((twelveEndpointSlope i : ℝ) * (c.left : ℝ) -
              (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * (c.left : ℝ) -
              (twelveCellFloor c j : ℝ))) -
              ((twelveEndpointSlope j : ℝ) -
                (twelveEndpointSlope i : ℝ)) * (z - (c.left : ℝ)) := by ring
      rw [heq]
      linarith
    linarith [hLeftR']
  · have hgt : twelveEndpointSlope j < twelveEndpointSlope i := by
      rcases lt_or_gt_of_ne hsne with h | h
      · exact (False.elim (hs h))
      · exact h
    have hgtR : (twelveEndpointSlope j : ℝ) <
        (twelveEndpointSlope i : ℝ) := by exact_mod_cast hgt
    have hpos : 0 < ((twelveEndpointSlope i : ℝ) -
        (twelveEndpointSlope j : ℝ)) * ((c.right : ℝ) - z) :=
      mul_pos (sub_pos.mpr hgtR) (sub_pos.mpr hzr)
    have hdiff :
        ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) <
        ((twelveEndpointSlope i : ℝ) * (c.right : ℝ) -
            (twelveCellFloor c i : ℝ)) -
            ((twelveEndpointSlope j : ℝ) * (c.right : ℝ) -
            (twelveCellFloor c j : ℝ)) := by
      have heq :
          ((twelveEndpointSlope i : ℝ) * z - (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * z - (twelveCellFloor c j : ℝ)) =
            (((twelveEndpointSlope i : ℝ) * (c.right : ℝ) -
              (twelveCellFloor c i : ℝ)) -
              ((twelveEndpointSlope j : ℝ) * (c.right : ℝ) -
              (twelveCellFloor c j : ℝ))) -
              ((twelveEndpointSlope i : ℝ) -
                (twelveEndpointSlope j : ℝ)) * ((c.right : ℝ) - z) := by ring
      rw [heq]
      linarith
    linarith [hRightR']

theorem endpoint_lt_iff_rank_lt {c : TwelveCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i j : TwelveEndpoint) :
    twelveEndpointReal i z < twelveEndpointReal j z ↔
      (twelveRank c.rankCode i).val < (twelveRank c.rankCode j).val := by
  constructor
  · intro h
    by_contra hn
    have hinj : Function.Injective (twelveRank c.rankCode) := by
      rcases hc with ⟨_, _, _, _, _, h, _, _, _, _, _, _⟩
      exact List.nodup_ofFn.mp h
    by_cases heq : (twelveRank c.rankCode i).val =
        (twelveRank c.rankCode j).val
    · have hij : i = j := by
        apply hinj
        exact Fin.ext heq
      subst j
      exact (lt_irrefl _ h)
    · have hji : (twelveRank c.rankCode j).val <
          (twelveRank c.rankCode i).val := by omega
      exact (not_lt_of_ge (le_of_lt (endpoint_lt_of_rank_lt hc hzl hzr hji))) h
  · exact endpoint_lt_of_rank_lt hc hzl hzr

end TwelveCellCertificate

theorem twelveLayerShape_cost_scale (s : ℕ) (z y : ℝ) :
    (twelveLayerShape.scaleWeights s).cost z y = s * twelveLayerShape.cost z y :=
  twelveLayerShape.cost_scaleWeights s z y

end OddPiPowers

end
