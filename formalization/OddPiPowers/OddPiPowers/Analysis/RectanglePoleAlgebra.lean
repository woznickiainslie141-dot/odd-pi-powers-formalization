module

public import OddPiPowers.Analysis.RectanglePrimitives
public import Mathlib.Analysis.Complex.RemovableSingularity

/-! Finite boundary linearity and exact divided-difference pole reduction. -/

@[expose] public section

namespace OddPiPowers

open MeasureTheory

theorem RectangleIntegrable.add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (hg : RectangleIntegrable g a b c d) :
    RectangleIntegrable (fun z => f z + g z) a b c d :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top, hf.right.add hg.right, hf.left.add hg.left⟩

theorem RectangleIntegrable.const_mul {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (k : ℂ) :
    RectangleIntegrable (fun z => k * f z) a b c d :=
  ⟨hf.bottom.const_mul k, hf.top.const_mul k, hf.right.const_mul k, hf.left.const_mul k⟩

set_option backward.isDefEq.respectTransparency false in
theorem RectangleIntegrable.fun_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (a b c d : ℝ) (hf : ∀ i ∈ s, RectangleIntegrable (f i) a b c d) :
    RectangleIntegrable (fun z => ∑ i ∈ s, f i z) a b c d := by
  constructor
  · convert IntervalIntegrable.sum s (fun i hi => (hf i hi).bottom) using 1
    ext x
    simp only [Finset.sum_apply]
  · convert IntervalIntegrable.sum s (fun i hi => (hf i hi).top) using 1
    ext x
    simp only [Finset.sum_apply]
  · convert IntervalIntegrable.sum s (fun i hi => (hf i hi).right) using 1
    ext x
    simp only [Finset.sum_apply]
  · convert IntervalIntegrable.sum s (fun i hi => (hf i hi).left) using 1
    ext x
    simp only [Finset.sum_apply]

theorem rectangleIntegral_fun_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (a b c d : ℝ) (hf : ∀ i ∈ s, RectangleIntegrable (f i) a b c d) :
    rectangleIntegral (fun z => ∑ i ∈ s, f i z) a b c d =
      ∑ i ∈ s, rectangleIntegral (f i) a b c d := by
  unfold rectangleIntegral
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).bottom),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).top),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).right),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).left)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem rectangleIntegral_congr_nonpole (f g : ℂ → ℂ) (p a b c d : ℝ)
    (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ 0) (hd : d ≠ 0)
    (hfg : ∀ z : ℂ, z ≠ (p : ℂ) → f z = g z) :
    rectangleIntegral f a b c d = rectangleIntegral g a b c d := by
  have hbot : (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I)) =
      (fun x : ℝ => g ((x : ℂ) + (c : ℂ) * Complex.I)) := by
    funext x
    exact hfg _ (sub_ne_zero.mp (rectangle_horizontal_ne_pole p c x hc))
  have htop : (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (fun x : ℝ => g ((x : ℂ) + (d : ℂ) * Complex.I)) := by
    funext x
    exact hfg _ (sub_ne_zero.mp (rectangle_horizontal_ne_pole p d x hd))
  have hright : (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => g ((b : ℂ) + (y : ℂ) * Complex.I)) := by
    funext y
    exact hfg _ (sub_ne_zero.mp (rectangle_vertical_ne_pole p b y hb))
  have hleft : (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => g ((a : ℂ) + (y : ℂ) * Complex.I)) := by
    funext y
    exact hfg _ (sub_ne_zero.mp (rectangle_vertical_ne_pole p a y ha))
  unfold rectangleIntegral
  rw [hbot, htop, hright, hleft]

theorem entire_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (p : ℂ) :
    Differentiable ℂ (dslope f p) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (s := Set.univ) (c := p) Filter.univ_mem).mpr
    hf.differentiableOn

theorem pole_dslope_decomposition (f : ℂ → ℂ) (p : ℂ) (j : ℕ) (z : ℂ) (hz : z ≠ p) :
    f z / (z - p) ^ (j + 1) =
      dslope f p z / (z - p) ^ j + f p * (1 / (z - p) ^ (j + 1)) := by
  have h := sub_smul_dslope f p z
  simp only [smul_eq_mul] at h
  have he : f z = (z - p) * dslope f p z + f p := (sub_eq_iff_eq_add.mp h.symm)
  rw [he]
  field_simp [sub_ne_zero.mpr hz, pow_succ]
  ring

end OddPiPowers
