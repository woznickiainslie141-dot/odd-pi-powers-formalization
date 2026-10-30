module
public import OddPiPowers.L99.Analysis.TwentyEightLayerActualRates
public import OddPiPowers.L99.Analysis.L99CentralCertificate00
public import OddPiPowers.L99.Analysis.L99CentralCertificate01
public import OddPiPowers.L99.Analysis.L99CentralCertificate02
public import OddPiPowers.L99.Analysis.L99CentralCertificate03
public import OddPiPowers.L99.Analysis.L99CentralCertificate04
public import OddPiPowers.L99.Analysis.L99CentralCertificate05
public import OddPiPowers.L99.Analysis.L99CentralCertificate06
public import OddPiPowers.L99.Analysis.L99CentralCertificate07
public import OddPiPowers.L99.Analysis.L99CentralCertificate08
public import OddPiPowers.L99.Analysis.L99CentralCertificate09
public import OddPiPowers.L99.Analysis.L99CentralCertificate10
public import OddPiPowers.L99.Analysis.L99CentralCertificate11
public import OddPiPowers.L99.Analysis.L99CentralCertificate12
public import OddPiPowers.L99.Analysis.L99CentralCertificate13
public import OddPiPowers.L99.Analysis.L99CentralCertificate14
public import OddPiPowers.L99.Analysis.L99CentralCertificate15
public import OddPiPowers.L99.Analysis.L99CentralCertificate16
public import OddPiPowers.L99.Analysis.L99CentralCertificate17
public import OddPiPowers.L99.Analysis.L99CentralCertificate18
public import OddPiPowers.L99.Analysis.L99CentralCertificate19
public import OddPiPowers.L99.Analysis.L99CentralCertificate20
public import OddPiPowers.L99.Analysis.L99CentralCertificate21
public import OddPiPowers.L99.Analysis.L99CentralCertificate22
public import OddPiPowers.L99.Analysis.L99CentralCertificate23
public import OddPiPowers.L99.Analysis.L99CentralCertificate24
public import OddPiPowers.L99.Analysis.L99CentralCertificate25
public import OddPiPowers.L99.Analysis.L99CentralCertificate26
public import OddPiPowers.L99.Analysis.L99CentralCertificate27
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace OddPiPowers.L99
open scoped BigOperators

theorem l99_scaled_central_sum_lower : ((400954432187 / 500000000) : ℝ) ≤
    ∑ a : Fin (43 * 4), centralIntervalRate
      (((99 - 2 * scaledTwentyEightLayerOffset 4 a : ℕ) : ℝ) / 99) (1801 / 20) := by
  rw [scaledTwentyEightLayer_central_sum 4 (by norm_num) (1801 / 20)]
  norm_num [Fin.sum_univ_succ]
  have h00 := l99CentralInterval00_lower
  have h01 := l99CentralInterval01_lower
  have h02 := l99CentralInterval02_lower
  have h03 := l99CentralInterval03_lower
  have h04 := l99CentralInterval04_lower
  have h05 := l99CentralInterval05_lower
  have h06 := l99CentralInterval06_lower
  have h07 := l99CentralInterval07_lower
  have h08 := l99CentralInterval08_lower
  have h09 := l99CentralInterval09_lower
  have h10 := l99CentralInterval10_lower
  have h11 := l99CentralInterval11_lower
  have h12 := l99CentralInterval12_lower
  have h13 := l99CentralInterval13_lower
  have h14 := l99CentralInterval14_lower
  have h15 := l99CentralInterval15_lower
  have h16 := l99CentralInterval16_lower
  have h17 := l99CentralInterval17_lower
  have h18 := l99CentralInterval18_lower
  have h19 := l99CentralInterval19_lower
  have h20 := l99CentralInterval20_lower
  have h21 := l99CentralInterval21_lower
  have h22 := l99CentralInterval22_lower
  have h23 := l99CentralInterval23_lower
  have h24 := l99CentralInterval24_lower
  have h25 := l99CentralInterval25_lower
  have h26 := l99CentralInterval26_lower
  have h27 := l99CentralInterval27_lower
  norm_num at h00 h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
  linarith

theorem l99_actualDecay_lower : ((9789173 / 20000) : ℝ) ≤
    actualDecay 171 99 (scaledTwentyEightLayerOffset 4) (1801 / 20) := by
  have hsum := l99_scaled_central_sum_lower
  have hpi := Real.pi_lt_d20
  unfold actualDecay
  linarith

theorem l99_actualGrowth_upper : actualGrowth 171 99 (scaledTwentyEightLayerOffset 4) ≤ ((13452441 / 50000) : ℝ) := by
  have hl := Real.log_two_lt_d9
  have hshape := scaledTwentyEightLayer_shapeRelativeLength 4 (by norm_num)
  unfold actualGrowth
  rw [hshape]
  norm_num at hl ⊢
  linarith

end OddPiPowers.L99
