module

public import OddPiPowers.Analysis.ActualReducedDiskHeight
public import OddPiPowers.Analysis.CentralRemainderRate

/-! Both exponential rates for an actual scaled family after integral reduction. -/

@[expose] public section

namespace OddPiPowers

open Filter Polynomial
open scoped Topology BigOperators

theorem quotient_exp_bound {a d u v n : ℝ} (hd : 0 < d)
    (ha : a ≤ Real.exp (u * n)) (hdiv : Real.exp (v * n) ≤ d) :
    a / d ≤ Real.exp ((u - v) * n) := by
  calc
    a / d ≤ Real.exp (u * n) / d := div_le_div_of_nonneg_right ha hd.le
    _ ≤ Real.exp (u * n) / Real.exp (v * n) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hdiv
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

noncomputable def actualGrowth (m L : ℕ) (A : Fin (m + 1) → ℕ) : ℝ :=
  (m : ℝ) + shapeRelativeLength L A * Real.log 2

noncomputable def actualDecay (m L : ℕ) (A : Fin (m + 1) → ℕ) (Y : ℝ) : ℝ :=
  (∑ a : Fin (m + 1), centralIntervalRate (((L - 2 * A a : ℕ) : ℝ) / L) Y) -
    (Real.pi / 2) * Y - (m : ℝ)

theorem scaled_denominator_degree_eventually (m L : ℕ) (hL : 0 < L)
    (A : Fin (m + 1) → ℕ) (hA : ∀ a, 2 * A a < L)
    (P : ℕ → ActualIntervals (m + 1))
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N) :
    ∀ᶠ N : ℕ in atTop, 2 * (((m + 1) - 1) + 2) ≤ (P N).denominator.natDegree := by
  classical
  let a : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
  filter_upwards [eventually_ge_atTop (2 * (m + 2))] with N hN
  have hw : 1 ≤ L - 2 * A a := by have := hA a; omega
  have hlen : N ≤ (P N).length a := by
    rw [ActualIntervals.scaled_length P L A hn hl]
    simpa using Nat.mul_le_mul_right N hw
  have hsum : ((P N).interval a).card ≤ ∑ b : Fin (m + 1), ((P N).interval b).card :=
    Finset.single_le_sum (f := fun b : Fin (m + 1) => ((P N).interval b).card)
      (fun b hb => Nat.zero_le _) (Finset.mem_univ a)
  rw [(P N).interval_card_eq_length_add_one] at hsum
  rw [(P N).denominator_natDegree, (P N).totalMultiplicity_eq_sum_interval_card]
  omega

theorem reduced_disk_heights_eventually (m L : ℕ) (hL : 0 < L)
    (A : Fin (m + 1) → ℕ) (P : ℕ → ActualIntervals (m + 1))
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (γ : ℝ) (hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp ((γ - ε) * ((L * N : ℕ) : ℝ)) ≤ ((P N).actualAuxiliaryPrimeDivisor : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (∀ h z, ‖z‖ ≤ 2 → ‖(complexPolynomial (reducedGaussianRow (P N) h)).eval z‖ ≤
        Real.exp ((actualGrowth m L A - γ + η) * ((L * N : ℕ) : ℝ))) ∧
      (∀ h z, ‖z‖ ≤ 2 → ‖(complexDividedDifference m (reducedGaussianRow (P N) h)).eval z‖ ≤
        Real.exp ((actualGrowth m L A - γ + η) * ((L * N : ℕ) : ℝ))) := by
  have hη2 : 0 < η / 2 := by linarith
  have hH := actualConstantHeight_eventually_exp P L hL A hn hl (balancedDiskConstant m)
    (balancedDiskConstant_pos m) hη2
  simp only [Nat.add_sub_cancel_right] at hH
  filter_upwards [hH, hdiv (η / 2) hη2] with N hH hD
  have hd : (0 : ℝ) < (P N).actualAuxiliaryPrimeDivisor := by
    exact_mod_cast (P N).actualAuxiliaryPrimeDivisor_pos
  have hb : balancedDiskConstant m * actualReducedHeight (P N) ≤
      Real.exp ((actualGrowth m L A - γ + η) * ((L * N : ℕ) : ℝ)) := by
    unfold actualReducedHeight
    rw [← mul_div_assoc]
    have ht := quotient_exp_bound hd hH hD
    convert ht using 1 <;> unfold actualGrowth <;> congr 1 <;> ring
  exact ⟨fun h z hz => (reduced_row_disk_bound m (P N) h z hz).trans hb,
    fun h z hz => (reduced_difference_disk_bound m (P N) h z hz).trans hb⟩

theorem reduced_remainders_eventually (m L : ℕ) (hL : 0 < L)
    (A : Fin (m + 1) → ℕ) (hA : ∀ a, 2 * A a < L)
    (P : ℕ → ActualIntervals (m + 1))
    (hn : ∀ N, (P N).n = L * N) (hl : ∀ N a, (P N).left a = A a * N)
    (Y : ℝ) (hY : 1 / 2 < Y)
    (γ : ℝ) (hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp ((γ - ε) * ((L * N : ℕ) : ℝ)) ≤ ((P N).actualAuxiliaryPrimeDivisor : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ h : Fin (m + 1),
      ‖(complexPolynomial (reducedGaussianRow (P N) h)).eval lambda‖ ≤
        Real.exp (-(actualDecay m L A Y + γ - η) * ((L * N : ℕ) : ℝ)) := by
  have hη2 : 0 < η / 2 := by linarith
  have hR := ActualIntervals.actualRows_eventually_exp_upper P (Nat.succ_pos m) L hL A hA
    hn hl (scaled_denominator_degree_eventually m L hL A hA P hn hl) Y hY hη2
  simp only [Nat.add_sub_cancel_right] at hR
  filter_upwards [hR, hdiv (η / 2) hη2] with N hR hD h
  have hd : (0 : ℝ) < (P N).actualAuxiliaryPrimeDivisor := by
    exact_mod_cast (P N).actualAuxiliaryPrimeDivisor_pos
  simp only [complexPolynomial, Polynomial.eval_map, reducedGaussianRow_eval]
  rw [(P N).reducedAuxiliaryRow_norm]
  have ht := quotient_exp_bound hd (hR h) hD
  convert ht using 1 <;> unfold actualDecay <;> congr 1 <;> ring

end OddPiPowers
