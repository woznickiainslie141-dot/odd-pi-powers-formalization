module

public import OddPiPowers.Analysis.BalancedDiskHeight
public import OddPiPowers.Analysis.CentralRemainderRate

/-! The actual balanced construction supplies every field of AuxiliaryFamily. -/

@[expose] public section

namespace OddPiPowers

open Filter Polynomial
open scoped Topology BigOperators

noncomputable def balancedDecay (m : ℕ) (Y : ℝ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) * centralIntervalRate 1 Y - (Real.pi / 2) * Y - (m : ℝ)

noncomputable def balancedGrowth (m : ℕ) : ℝ :=
  (m : ℝ) + ((m + 1 : ℕ) : ℝ) * Real.log 2

theorem balancedGrowth_nonneg (m : ℕ) : 0 ≤ balancedGrowth m := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold balancedGrowth
  positivity

theorem balanced_complexPolynomial_eval (m n : ℕ) (h : Fin (m + 1)) (z : ℂ) :
    (complexPolynomial (balancedGaussianRows m n h)).eval z =
      ∑ j : Fin (m + 1), (actualAuxiliary (balancedActualFamily (m + 1) n) h j).eval₂
        (Rat.castHom ℂ) Complex.I * z ^ j.val := by
  simp only [complexPolynomial, balancedGaussianRows, Polynomial.eval_map, gaussianAuxiliaryRow_eval]

theorem balanced_remainders_eventually (m : ℕ) (Y : ℝ) (hY : 1 / 2 < Y)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ h : Fin (m + 1),
      ‖(complexPolynomial (balancedGaussianRows m n h)).eval lambda‖ ≤
        Real.exp (-(balancedDecay m Y - η) * (n : ℝ)) := by
  have hd : ∀ᶠ n : ℕ in atTop,
      2 * (((m + 1) - 1) + 2) ≤ (balancedActualFamily (m + 1) n).denominator.natDegree := by
    filter_upwards [eventually_ge_atTop (2 * (m + 2))] with n hn
    have ht := (balancedActualFamily (m + 1) n).denominator_natDegree_ge_n_add_one
      (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) rfl
    change n + 1 ≤ (balancedActualFamily (m + 1) n).denominator.natDegree at ht
    omega
  have ht := ActualIntervals.actualRows_eventually_exp_upper (balancedActualFamily (m + 1))
    (Nat.succ_pos m) 1 (by norm_num) (fun _ => 0) (fun a => by norm_num)
    (fun n => by simp [balancedActualFamily]) (fun n a => by simp [balancedActualFamily])
    hd Y hY hη
  simp only [Nat.one_mul, Nat.cast_one, div_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.add_sub_cancel_right] at ht
  filter_upwards [ht] with n hn h
  rw [balanced_complexPolynomial_eval]
  convert hn h using 2
  congr 1
  unfold balancedDecay
  ring

theorem balanced_actual_auxiliaryFamily (m : ℕ) (Y : ℝ) (hY : 1 / 2 < Y) :
    AuxiliaryFamily m 1 (balancedDecay m Y) (balancedGrowth m) (balancedGaussianRows m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr h
    simpa only [Nat.one_mul, balancedGaussianRows] using
      gaussianAuxiliaryRow_degree_for_transfer m (balancedActualFamily (m + 1) r) h
  · intro r hr
    simp only [Nat.one_mul]
    have he : balancedGaussianRows m r = gaussianAuxiliaryRow (balancedActualFamily (m + 1) r) := by
      funext h
      rfl
    rw [he]
    exact gaussianAuxiliaryRow_coefficientMatrix_det_ne_zero m (balancedActualFamily (m + 1) r)
  · intro η hη
    have hR := balanced_remainders_eventually m Y hY hη
    have hH := balanced_disk_heights_eventually m hη
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hR.and hH)
    refine ⟨N, ?_⟩
    intro r hr hNr
    have hall := hN r (by simpa only [Nat.one_mul] using hNr)
    simpa only [Nat.one_mul, balancedGrowth] using ⟨hall.1, hall.2.1, hall.2.2⟩

end OddPiPowers
