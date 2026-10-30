module

public import OddPiPowers.Analysis.ActualCentralBound
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact logarithms of the finite actual center product. Every endpoint
is retained; no Riemann-sum or Stirling error is assumed. -/

@[expose] public section

namespace OddPiPowers

theorem log_norm_horizontal_factor (u Y : ℝ) :
    Real.log ‖((u : ℂ) + Complex.I * (Y : ℂ))‖ =
      (1 / 2 : ℝ) * Real.log (u ^ 2 + Y ^ 2) := by
  have hs : ‖((u : ℂ) + Complex.I * (Y : ℂ))‖ ^ 2 = u ^ 2 + Y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_horizontal_factor]
  have ht := Real.log_pow ‖((u : ℂ) + Complex.I * (Y : ℂ))‖ 2
  rw [hs] at ht
  norm_num at ht
  linarith

namespace ActualIntervals

variable {M : ℕ} (P : ActualIntervals M)

theorem log_intervalFactorialProduct_norm :
    Real.log ‖P.intervalFactorialProduct‖ =
      ∑ a : Fin M, Real.log (Nat.factorial (P.length a) : ℝ) := by
  rw [P.intervalFactorialProduct_norm]
  exact Real.log_prod (fun a ha => by exact_mod_cast Nat.factorial_ne_zero (P.length a))

theorem log_normalizedHorizontalProduct_norm (Y : ℝ) (hY : Y ≠ 0) :
    Real.log ‖P.normalizedHorizontalProduct Y 0‖ =
      (1 / 2 : ℝ) * ∑ a : Fin M, ∑ r ∈ P.interval a,
        Real.log (P.horizontalOffset r ^ 2 + Y ^ 2) := by
  classical
  have ht (r : ℕ) : ‖(((P.horizontalOffset r : ℝ) : ℂ) + Complex.I * (Y : ℂ))‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro he
    have hi := congrArg Complex.im he
    exact hY (by simpa using hi)
  simp only [normalizedHorizontalProduct, zero_add, norm_prod]
  rw [Real.log_prod (fun a ha => Finset.prod_ne_zero_iff.mpr (fun r hr => ht r))]
  simp_rw [Real.log_prod (fun r hr => ht r), log_norm_horizontal_factor]
  simp only [Finset.mul_sum]

theorem log_horizontalDenominator_center (hn : 0 < P.n) (Y : ℝ) (hY : Y ≠ 0) :
    Real.log ‖P.horizontalDenominator Y 0‖ =
      (P.totalMultiplicity : ℝ) * Real.log (P.n : ℝ) +
        (1 / 2 : ℝ) * ∑ a : Fin M, ∑ r ∈ P.interval a,
          Real.log (P.horizontalOffset r ^ 2 + Y ^ 2) := by
  rw [P.horizontalDenominator_eq hn, norm_mul, norm_pow, Complex.norm_natCast,
    Real.log_mul (pow_ne_zero _ (by exact_mod_cast hn.ne'))
      (norm_ne_zero_iff.mpr (P.normalizedHorizontalProduct_ne_zero Y 0 hY)),
    Real.log_pow, P.log_normalizedHorizontalProduct_norm Y hY]

noncomputable def centralLogRatio (Y : ℝ) : ℝ :=
  Real.log ‖P.intervalFactorialProduct‖ - Real.log ‖P.horizontalDenominator Y 0‖

theorem centralLogRatio_eq_finite_sum (hn : 0 < P.n) (Y : ℝ) (hY : Y ≠ 0) :
    P.centralLogRatio Y =
      (∑ a : Fin M, Real.log (Nat.factorial (P.length a) : ℝ)) -
        (P.totalMultiplicity : ℝ) * Real.log (P.n : ℝ) -
          (1 / 2 : ℝ) * ∑ a : Fin M, ∑ r ∈ P.interval a,
            Real.log (P.horizontalOffset r ^ 2 + Y ^ 2) := by
  rw [centralLogRatio, P.log_intervalFactorialProduct_norm,
    P.log_horizontalDenominator_center hn Y hY]
  ring

theorem exp_centralLogRatio (hn : 0 < P.n) (Y : ℝ) (hY : Y ≠ 0) :
    Real.exp (P.centralLogRatio Y) =
      ‖P.intervalFactorialProduct‖ / ‖P.horizontalDenominator Y 0‖ := by
  rw [centralLogRatio, Real.exp_sub, Real.exp_log P.intervalFactorialProduct_norm_pos,
    Real.exp_log (norm_pos_iff.mpr (P.horizontalDenominator_ne_zero hn Y 0 hY))]

theorem log_centralRemainderBound (hn : 0 < P.n) (m h : ℕ) (theta Y : ℝ)
    (hY : 1 / 2 < Y) :
    Real.log (P.centralRemainderBound m h theta Y) =
      Real.log (((auxiliaryCommonScale M P.n : ℚ) : ℝ)) +
        Real.log (horizontalMajorantConstant (horizontalB Y) (Y + 1 / 2) m) +
          ((h + 1 : ℕ) : ℝ) * Real.log (P.n : ℝ) +
            |theta| * ((P.n : ℝ) * Y) + P.centralLogRatio Y := by
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hS := auxiliaryCommonScale_cast_pos M P.n
  have hA := horizontalMajorantConstant_pos (B := horizontalB Y)
    (show 0 ≤ Y + 1 / 2 by linarith) m
  have hF := P.intervalFactorialProduct_norm_pos
  have hQ := norm_pos_iff.mpr (P.horizontalDenominator_ne_zero hn Y 0 (by linarith))
  have hnP : 0 < (P.n : ℝ) ^ (h + 1) := pow_pos hnR _
  unfold centralRemainderBound centralLogRatio
  rw [Real.log_div (by positivity) hQ.ne',
    Real.log_mul (by positivity) hF.ne',
    Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (by positivity) hnP.ne', Real.log_mul hS.ne' hA.ne',
    Real.log_pow, Real.log_exp]
  ring

end ActualIntervals
end OddPiPowers
