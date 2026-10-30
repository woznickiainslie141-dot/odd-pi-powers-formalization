module
public import OddPiPowers.L99.Arithmetic.TwentyEightLayerCellDefs
@[expose] public section
namespace OddPiPowers.L99
open scoped BigOperators

private theorem twentyEightNat_affine_le (a b u v n d : ℕ) (hd : 0 < d)
    (h : a * n + v * d ≤ b * n + u * d) :
    (a : ℚ) * ((n : ℚ) / d) - u ≤ (b : ℚ) * ((n : ℚ) / d) - v := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hdne : (d : ℚ) ≠ 0 := ne_of_gt hdQ
  have hQ : (a : ℚ) * n + v * d ≤ (b : ℚ) * n + u * d := by
    exact_mod_cast h
  apply (mul_le_mul_iff_left₀ hdQ).mp
  simp only [sub_mul, mul_assoc, div_mul_cancel₀ _ hdne]
  linarith

theorem TwentyEightCellCertificate.unit_interval_of_valid {c : TwentyEightCellCertificate}
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

theorem TwentyEightCellCertificate.floor_bounds_rat {c : TwentyEightCellCertificate}
    (hc : c.Valid) (i : TwentyEightEndpoint) :
    (twentyEightCellFloor c i : ℚ) ≤ (twentyEightEndpointSlope i : ℚ) * c.left ∧
      (twentyEightEndpointSlope i : ℚ) * c.right ≤ (twentyEightCellFloor c i : ℚ) + 1 := by
  rcases hc with ⟨hld, hrd, _, _, _, _, _, hf, _, _, _, _⟩
  have hldQ : (0 : ℚ) < c.leftDenominator := by exact_mod_cast hld
  have hrdQ : (0 : ℚ) < c.rightDenominator := by exact_mod_cast hrd
  constructor
  · change (twentyEightFloorDigit c.floorCode i : ℚ) ≤
      (twentyEightEndpointSlope i : ℚ) * ((c.leftNumerator : ℚ) / c.leftDenominator)
    rw [← mul_div_assoc, le_div_iff₀ hldQ]
    exact_mod_cast (hf i).1
  · change (twentyEightEndpointSlope i : ℚ) *
        ((c.rightNumerator : ℚ) / c.rightDenominator) ≤
      (twentyEightFloorDigit c.floorCode i : ℚ) + 1
    rw [← mul_div_assoc, div_le_iff₀ hrdQ]
    exact_mod_cast (hf i).2

theorem TwentyEightCellCertificate.adjacent_bounds_rat {c : TwentyEightCellCertificate}
    (hc : c.Valid) (k : Fin 55) :
    twentyEightEndpointAffine c (twentyEightOrderEndpoint c.orderCode k.castSucc) c.left ≤
        twentyEightEndpointAffine c (twentyEightOrderEndpoint c.orderCode k.succ) c.left ∧
    twentyEightEndpointAffine c (twentyEightOrderEndpoint c.orderCode k.castSucc) c.right ≤
        twentyEightEndpointAffine c (twentyEightOrderEndpoint c.orderCode k.succ) c.right := by
  rcases hc with ⟨hld, hrd, _, _, _, _, _, _, ha, _, _, _⟩
  constructor
  · simpa [twentyEightEndpointAffine, TwentyEightCellCertificate.left, twentyEightCellFloor] using
      twentyEightNat_affine_le
        (twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.castSucc))
        (twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.succ))
        (twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.castSucc))
        (twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.succ))
        c.leftNumerator c.leftDenominator hld (ha k).1
  · simpa [twentyEightEndpointAffine, TwentyEightCellCertificate.right, twentyEightCellFloor] using
      twentyEightNat_affine_le
        (twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.castSucc))
        (twentyEightEndpointSlope (twentyEightOrderEndpoint c.orderCode k.succ))
        (twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.castSucc))
        (twentyEightFloorDigit c.floorCode (twentyEightOrderEndpoint c.orderCode k.succ))
        c.rightNumerator c.rightDenominator hrd (ha k).2

private theorem monotone_fin56 {α : Type} [Preorder α] (f : Fin 56 → α)
    (hstep : ∀ k : Fin 55, f k.castSucc ≤ f k.succ) :
    ∀ a b : Fin 56, a.val ≤ b.val → f a ≤ f b := by
  intro a b hab
  let d := b.val - a.val
  have hd : b.val = a.val + d := by simp [d]; omega
  have aux : ∀ d (b : Fin 56), b.val = a.val + d → f a ≤ f b := by
    intro n
    induction n with
    | zero =>
      intro b hb
      have hEq : b = a := Fin.ext (by simpa using hb)
      subst b
      exact le_rfl
    | succ n ih =>
      intro b hb
      let mid : Fin 56 := ⟨a.val + n, by omega⟩
      have hmid : mid.val = a.val + n := by simp [mid]
      have hfirst := ih mid hmid
      have hlt : mid.val < 55 := by simp [mid]; omega
      let k : Fin 55 := ⟨mid.val, hlt⟩
      have hadj := hstep k
      have hleft : k.castSucc = mid := by apply Fin.ext; rfl
      have hright : k.succ = b := by apply Fin.ext; simp [k]; omega
      rw [hleft, hright] at hadj
      exact hfirst.trans hadj
  exact aux d b hd

namespace TwentyEightCellCertificate

theorem floor_eq_of_valid {c : TwentyEightCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i : TwentyEightEndpoint) :
    Int.floor ((twentyEightEndpointSlope i : ℝ) * z) = twentyEightCellFloor c i := by
  have hfloor := floor_bounds_rat hc i
  have hs0 : (0 : ℝ) ≤ (twentyEightEndpointSlope i : ℝ) := by positivity
  have hqlo : (twentyEightCellFloor c i : ℝ) ≤
      (twentyEightEndpointSlope i : ℝ) * (c.left : ℝ) := by
    exact_mod_cast hfloor.1
  have hqhi : (twentyEightEndpointSlope i : ℝ) * (c.right : ℝ) ≤
      (twentyEightCellFloor c i : ℝ) + 1 := by
    exact_mod_cast hfloor.2
  have hlo : (twentyEightCellFloor c i : ℝ) ≤
      (twentyEightEndpointSlope i : ℝ) * z := by
    exact hqlo.trans (mul_le_mul_of_nonneg_left (le_of_lt hzl) hs0)
  have hhi : (twentyEightEndpointSlope i : ℝ) * z <
      (twentyEightCellFloor c i : ℝ) + 1 := by
    by_cases hs : twentyEightEndpointSlope i = 0
    · have hq : twentyEightCellFloor c i = 0 := by
        have hqlo' : (twentyEightCellFloor c i : ℝ) ≤ 0 := by
          simpa [hs] using hqlo
        have hqnn : (0 : ℝ) ≤ (twentyEightCellFloor c i : ℝ) := by
          have hI : (0 : ℤ) ≤ twentyEightCellFloor c i := by
            unfold twentyEightCellFloor
            exact Int.natCast_nonneg _
          exact_mod_cast hI
        exact_mod_cast le_antisymm hqlo' hqnn
      rw [hs, hq]
      norm_num
    · have hspos : (0 : ℝ) < (twentyEightEndpointSlope i : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hs
      have hmul : (twentyEightEndpointSlope i : ℝ) * z <
          (twentyEightEndpointSlope i : ℝ) * (c.right : ℝ) :=
        mul_lt_mul_of_pos_left hzr hspos
      exact hmul.trans_le hqhi
  apply Int.floor_eq_iff.mpr
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem endpoint_eq_affine_of_valid {c : TwentyEightCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i : TwentyEightEndpoint) :
    twentyEightEndpointReal i z =
      (twentyEightEndpointSlope i : ℝ) * z - (twentyEightCellFloor c i : ℝ) := by
  simp [twentyEightEndpointReal, Int.fract,
    floor_eq_of_valid hc hzl hzr i]

theorem endpoint_lt_of_rank_lt {c : TwentyEightCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    {i j : TwentyEightEndpoint}
    (hij : (twentyEightRank c.rankCode i).val < (twentyEightRank c.rankCode j).val) :
    twentyEightEndpointReal i z < twentyEightEndpointReal j z := by
  have hei := endpoint_eq_affine_of_valid hc hzl hzr i
  have hej := endpoint_eq_affine_of_valid hc hzl hzr j
  have hadj := adjacent_bounds_rat hc
  rcases hc with ⟨_, _, _, _, _, hnodup, horderInv, _, _, _, _, _⟩
  have hinj : Function.Injective (twentyEightRank c.rankCode) := by
    exact List.nodup_ofFn.mp hnodup
  have hne : i ≠ j := by
    intro h
    subst j
    exact (Nat.lt_irrefl _ hij)
  have hsne : twentyEightEndpointSlope i ≠ twentyEightEndpointSlope j := by
    intro h
    exact hne (twentyEightEndpointSlope_injective h)
  have horderI : twentyEightOrderEndpoint c.orderCode (twentyEightRank c.rankCode i) = i :=
    hinj (horderInv (twentyEightRank c.rankCode i))
  have horderJ : twentyEightOrderEndpoint c.orderCode (twentyEightRank c.rankCode j) = j :=
    hinj (horderInv (twentyEightRank c.rankCode j))
  have hLeft := monotone_fin56
    (fun r => twentyEightEndpointAffine c (twentyEightOrderEndpoint c.orderCode r) c.left)
    (fun k => (hadj k).1) (twentyEightRank c.rankCode i) (twentyEightRank c.rankCode j)
    (Nat.le_of_lt hij)
  have hRight := monotone_fin56
    (fun r => twentyEightEndpointAffine c (twentyEightOrderEndpoint c.orderCode r) c.right)
    (fun k => (hadj k).2) (twentyEightRank c.rankCode i) (twentyEightRank c.rankCode j)
    (Nat.le_of_lt hij)
  rw [horderI, horderJ] at hLeft hRight
  have hLeftR : (twentyEightEndpointAffine c i c.left : ℝ) ≤
      (twentyEightEndpointAffine c j c.left : ℝ) := by exact_mod_cast hLeft
  have hRightR : (twentyEightEndpointAffine c i c.right : ℝ) ≤
      (twentyEightEndpointAffine c j c.right : ℝ) := by exact_mod_cast hRight
  have hLeftR' : (twentyEightEndpointSlope i : ℝ) * (c.left : ℝ) -
      (twentyEightCellFloor c i : ℝ) ≤
      (twentyEightEndpointSlope j : ℝ) * (c.left : ℝ) -
      (twentyEightCellFloor c j : ℝ) := by
    simpa [twentyEightEndpointAffine] using hLeftR
  have hRightR' : (twentyEightEndpointSlope i : ℝ) * (c.right : ℝ) -
      (twentyEightCellFloor c i : ℝ) ≤
      (twentyEightEndpointSlope j : ℝ) * (c.right : ℝ) -
      (twentyEightCellFloor c j : ℝ) := by
    simpa [twentyEightEndpointAffine] using hRightR
  rw [hei, hej]
  by_cases hs : twentyEightEndpointSlope i < twentyEightEndpointSlope j
  · have hsR : (twentyEightEndpointSlope i : ℝ) <
        (twentyEightEndpointSlope j : ℝ) := by exact_mod_cast hs
    have hpos : 0 < ((twentyEightEndpointSlope j : ℝ) -
        (twentyEightEndpointSlope i : ℝ)) * ((z - (c.left : ℝ))) :=
      mul_pos (sub_pos.mpr hsR) (sub_pos.mpr hzl)
    have hdiff :
        ((twentyEightEndpointSlope i : ℝ) * z - (twentyEightCellFloor c i : ℝ)) -
            ((twentyEightEndpointSlope j : ℝ) * z - (twentyEightCellFloor c j : ℝ)) <
        ((twentyEightEndpointSlope i : ℝ) * (c.left : ℝ) -
            (twentyEightCellFloor c i : ℝ)) -
            ((twentyEightEndpointSlope j : ℝ) * (c.left : ℝ) -
            (twentyEightCellFloor c j : ℝ)) := by
      have heq :
          ((twentyEightEndpointSlope i : ℝ) * z - (twentyEightCellFloor c i : ℝ)) -
              ((twentyEightEndpointSlope j : ℝ) * z - (twentyEightCellFloor c j : ℝ)) =
            (((twentyEightEndpointSlope i : ℝ) * (c.left : ℝ) -
              (twentyEightCellFloor c i : ℝ)) -
              ((twentyEightEndpointSlope j : ℝ) * (c.left : ℝ) -
              (twentyEightCellFloor c j : ℝ))) -
              ((twentyEightEndpointSlope j : ℝ) -
                (twentyEightEndpointSlope i : ℝ)) * (z - (c.left : ℝ)) := by ring
      rw [heq]
      linarith
    linarith [hLeftR']
  · have hgt : twentyEightEndpointSlope j < twentyEightEndpointSlope i := by
      rcases lt_or_gt_of_ne hsne with h | h
      · exact (False.elim (hs h))
      · exact h
    have hgtR : (twentyEightEndpointSlope j : ℝ) <
        (twentyEightEndpointSlope i : ℝ) := by exact_mod_cast hgt
    have hpos : 0 < ((twentyEightEndpointSlope i : ℝ) -
        (twentyEightEndpointSlope j : ℝ)) * ((c.right : ℝ) - z) :=
      mul_pos (sub_pos.mpr hgtR) (sub_pos.mpr hzr)
    have hdiff :
        ((twentyEightEndpointSlope i : ℝ) * z - (twentyEightCellFloor c i : ℝ)) -
            ((twentyEightEndpointSlope j : ℝ) * z - (twentyEightCellFloor c j : ℝ)) <
        ((twentyEightEndpointSlope i : ℝ) * (c.right : ℝ) -
            (twentyEightCellFloor c i : ℝ)) -
            ((twentyEightEndpointSlope j : ℝ) * (c.right : ℝ) -
            (twentyEightCellFloor c j : ℝ)) := by
      have heq :
          ((twentyEightEndpointSlope i : ℝ) * z - (twentyEightCellFloor c i : ℝ)) -
              ((twentyEightEndpointSlope j : ℝ) * z - (twentyEightCellFloor c j : ℝ)) =
            (((twentyEightEndpointSlope i : ℝ) * (c.right : ℝ) -
              (twentyEightCellFloor c i : ℝ)) -
              ((twentyEightEndpointSlope j : ℝ) * (c.right : ℝ) -
              (twentyEightCellFloor c j : ℝ))) -
              ((twentyEightEndpointSlope i : ℝ) -
                (twentyEightEndpointSlope j : ℝ)) * ((c.right : ℝ) - z) := by ring
      rw [heq]
      linarith
    linarith [hRightR']

theorem endpoint_lt_iff_rank_lt {c : TwentyEightCellCertificate} (hc : c.Valid)
    {z : ℝ} (hzl : (c.left : ℝ) < z) (hzr : z < (c.right : ℝ))
    (i j : TwentyEightEndpoint) :
    twentyEightEndpointReal i z < twentyEightEndpointReal j z ↔
      (twentyEightRank c.rankCode i).val < (twentyEightRank c.rankCode j).val := by
  constructor
  · intro h
    by_contra hn
    have hinj : Function.Injective (twentyEightRank c.rankCode) := by
      rcases hc with ⟨_, _, _, _, _, h, _, _, _, _, _, _⟩
      exact List.nodup_ofFn.mp h
    by_cases heq : (twentyEightRank c.rankCode i).val =
        (twentyEightRank c.rankCode j).val
    · have hij : i = j := by
        apply hinj
        exact Fin.ext heq
      subst j
      exact (lt_irrefl _ h)
    · have hji : (twentyEightRank c.rankCode j).val <
          (twentyEightRank c.rankCode i).val := by omega
      exact (not_lt_of_ge (le_of_lt (endpoint_lt_of_rank_lt hc hzl hzr hji))) h
  · exact endpoint_lt_of_rank_lt hc hzl hzr

end TwentyEightCellCertificate

theorem twentyEightLayerShape_cost_scale (s : ℕ) (z y : ℝ) :
    (twentyEightLayerShape.scaleWeights s).cost z y = s * twentyEightLayerShape.cost z y :=
  twentyEightLayerShape.cost_scaleWeights s z y

end OddPiPowers.L99

end
