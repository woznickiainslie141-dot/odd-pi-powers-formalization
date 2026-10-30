module

public import OddPiPowers.Analysis.TwelveLayerActualRates
public import OddPiPowers.Analysis.P6CentralCertificate00
public import OddPiPowers.Analysis.P6CentralCertificate01
public import OddPiPowers.Analysis.P6CentralCertificate02
public import OddPiPowers.Analysis.P6CentralCertificate03
public import OddPiPowers.Analysis.P6CentralCertificate04
public import OddPiPowers.Analysis.P6CentralCertificate05
public import OddPiPowers.Analysis.P6CentralCertificate06
public import OddPiPowers.Analysis.P6CentralCertificate07
public import OddPiPowers.Analysis.P6CentralCertificate08
public import OddPiPowers.Analysis.P6CentralCertificate09
public import OddPiPowers.Analysis.P6CentralCertificate10
public import OddPiPowers.Analysis.P6CentralCertificate11
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Draft assembly of P6 fixed-height one-sided numerical rate bounds.
All imported numerical certificate drafts require their own kernel checks. -/

@[expose] public section

namespace OddPiPowers

open scoped BigOperators

theorem p6_scaled_central_sum_lower :
    (9578159265851 / 10000000000 : ℝ) ≤
      ∑ a : Fin (17 * 11), centralIntervalRate
        (((69 - 2 * scaledTwelveLayerOffset 11 a : ℕ) : ℝ) / 69) (2113 / 20) := by
  rw [scaledTwelveLayer_central_sum 11 (by norm_num) (2113 / 20)]
  norm_num [Fin.sum_univ_succ]
  have h00 := p6CentralInterval00_lower
  have h01 := p6CentralInterval01_lower
  have h02 := p6CentralInterval02_lower
  have h03 := p6CentralInterval03_lower
  have h04 := p6CentralInterval04_lower
  have h05 := p6CentralInterval05_lower
  have h06 := p6CentralInterval06_lower
  have h07 := p6CentralInterval07_lower
  have h08 := p6CentralInterval08_lower
  have h09 := p6CentralInterval09_lower
  have h10 := p6CentralInterval10_lower
  have h11 := p6CentralInterval11_lower
  norm_num at h00 h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11
  linarith

theorem p6_actualDecay_lower :
    (605861294 / 1000000 : ℝ) ≤
      actualDecay 186 69 (scaledTwelveLayerOffset 11) (2113 / 20) := by
  have hsum := p6_scaled_central_sum_lower
  have hpi := Real.pi_lt_d20
  unfold actualDecay
  linarith

theorem p6_actualGrowth_upper :
    actualGrowth 186 69 (scaledTwelveLayerOffset 11) ≤ (301032296 / 1000000 : ℝ) := by
  have hl := Real.log_two_lt_d9
  have hshape := scaledTwelveLayer_shapeRelativeLength 11 (by norm_num)
  unfold actualGrowth
  rw [hshape]
  norm_num at hl ⊢
  linarith

end OddPiPowers
