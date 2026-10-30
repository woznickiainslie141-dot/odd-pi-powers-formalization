module

public import OddPiPowers.Analysis.CentralRemainderRate
public import OddPiPowers.Analysis.TwelveLayerCentralBound

/-! Unconditional fixed-height central rates for all seventeen actual rows. -/

@[expose] public section

namespace OddPiPowers

open Filter
open scoped Topology BigOperators

def twelveLayerCentralOffset (a : Fin 17) : ℕ :=
  if a.val < 6 then 0 else a.val - 5

theorem twelveLayerCentralOffset_bound (a : Fin 17) :
    2 * twelveLayerCentralOffset a < 69 := by
  have ha := a.isLt
  unfold twelveLayerCentralOffset
  split_ifs <;> omega

theorem twelveLayerActualFamily_left_scaled (N : ℕ) (a : Fin 17) :
    (twelveLayerActualFamily N).left a = twelveLayerCentralOffset a * N := by
  by_cases ha : a.val < 6 <;>
    simp [twelveLayerActualFamily, twelveLayerCentralOffset, ha]

noncomputable def twelveLayerCentralSum (Y : ℝ) : ℝ :=
  ∑ a : Fin 17, centralIntervalRate (((69 - 2 * twelveLayerCentralOffset a : ℕ) : ℝ) / 69) Y

noncomputable def twelveLayerCentralDecay (Y : ℝ) : ℝ :=
  twelveLayerCentralSum Y - (Real.pi / 2) * Y - 16

theorem twelveLayer_centralLogRatio_tendsto (Y : ℝ) (hY : 0 < Y) :
    Tendsto (fun N : ℕ => (twelveLayerActualFamily N).centralLogRatio Y /
      ((69 * N : ℕ) : ℝ)) atTop (𝓝 (-twelveLayerCentralSum Y)) :=
  ActualIntervals.centralLogRatio_scaled_tendsto twelveLayerActualFamily 69 (by norm_num)
    twelveLayerCentralOffset twelveLayerCentralOffset_bound (fun N => rfl)
    twelveLayerActualFamily_left_scaled Y hY

theorem twelveLayer_centralRemainderBound_log_rate (Y : ℝ) (hY : 1 / 2 < Y) :
    Tendsto (fun N : ℕ => Real.log ((twelveLayerActualFamily N).centralRemainderBound
      16 16 (Real.pi / 2) Y) / ((69 * N : ℕ) : ℝ)) atTop
      (𝓝 (-twelveLayerCentralDecay Y)) := by
  have ht := ActualIntervals.centralRemainderBound_log_rate twelveLayerActualFamily 69
    (by norm_num) twelveLayerCentralOffset twelveLayerCentralOffset_bound (fun N => rfl)
    twelveLayerActualFamily_left_scaled 16 16 (Real.pi / 2) Y hY
  convert ht using 1
  congr 1
  simp only [twelveLayerCentralDecay, twelveLayerCentralSum,
    abs_of_pos (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))]
  norm_num
  ring

set_option backward.isDefEq.respectTransparency false in
theorem twelveLayer_actualRows_eventually_exp_upper (Y : ℝ) (hY : 1 / 2 < Y)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ h : Fin 17,
      ‖∑ j : Fin 17, (actualAuxiliary (twelveLayerActualFamily N) h j).eval₂
        (Rat.castHom ℂ) Complex.I * lambda ^ j.val‖ ≤
          Real.exp ((-twelveLayerCentralDecay Y + η) * ((69 * N : ℕ) : ℝ)) := by
  have hd : ∀ᶠ N : ℕ in atTop,
      2 * ((17 - 1) + 2) ≤ (twelveLayerActualFamily N).denominator.natDegree := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact twelveLayer_horizontal_degree N hN
  have ht := ActualIntervals.actualRows_eventually_exp_upper twelveLayerActualFamily
    (by norm_num) 69 (by norm_num) twelveLayerCentralOffset twelveLayerCentralOffset_bound
    (fun N => rfl) twelveLayerActualFamily_left_scaled hd Y hY hη
  filter_upwards [ht] with N hN h
  convert hN h using 2
  congr 1
  unfold twelveLayerCentralDecay twelveLayerCentralSum
  norm_num
  ring

theorem twelveLayer_reducedRows_eventually_exp_upper_of_divisor_rate
    (Y : ℝ) (hY : 1 / 2 < Y) (gamma : ℝ)
    (hD : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.exp ((gamma - ε) * ((69 * N : ℕ) : ℝ)) ≤
        ((twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ h : Fin 17,
      ‖(twelveLayerActualFamily N).reducedAuxiliaryRow h lambda‖ ≤
        Real.exp ((-(twelveLayerCentralDecay Y + gamma) + η) * ((69 * N : ℕ) : ℝ)) := by
  filter_upwards [twelveLayer_actualRows_eventually_exp_upper Y hY (half_pos hη),
    hD (η / 2) (half_pos hη)] with N hupper hdiv h
  have hDpos : (0 : ℝ) < (twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor := by
    exact_mod_cast (twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor_pos
  rw [(twelveLayerActualFamily N).reducedAuxiliaryRow_norm]
  calc
    _ ≤ Real.exp ((-twelveLayerCentralDecay Y + η / 2) * ((69 * N : ℕ) : ℝ)) /
        ((twelveLayerActualFamily N).actualAuxiliaryPrimeDivisor : ℝ) :=
      div_le_div_of_nonneg_right (hupper h) hDpos.le
    _ ≤ Real.exp ((-twelveLayerCentralDecay Y + η / 2) * ((69 * N : ℕ) : ℝ)) /
        Real.exp ((gamma - η / 2) * ((69 * N : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hdiv
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

theorem twelveLayer_reducedRows_eventually_exp_upper (Y : ℝ) (hY : 1 / 2 < Y)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ h : Fin 17,
      ‖(twelveLayerActualFamily N).reducedAuxiliaryRow h lambda‖ ≤
        Real.exp ((-(twelveLayerCentralDecay Y + (2 : ℝ) / 69) + η) * ((69 * N : ℕ) : ℝ)) :=
  twelveLayer_reducedRows_eventually_exp_upper_of_divisor_rate Y hY (2 / 69)
    (fun _ε hε => PrimeRates.twelveLayerActualFamily_eventually_exp_lower hε) hη

end OddPiPowers
