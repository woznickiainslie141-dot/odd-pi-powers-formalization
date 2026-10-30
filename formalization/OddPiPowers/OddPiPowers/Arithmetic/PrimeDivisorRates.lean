module

public import OddPiPowers.Arithmetic.PrimeNumberRates
public import OddPiPowers.Arithmetic.PrimeWindowDivisor

@[expose] public section

open scoped BigOperators Topology
open Filter Real

namespace OddPiPowers.PrimeRates

noncomputable def finiteWindowRate {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (L : ℕ) : ℝ :=
  (∑ i ∈ s, (W i).weight * (1 / (W i).lower - 1 / (W i).upper)) / L

/-- A fixed finite window certificate gives an unconditional one-sided
exponential lower bound, with arbitrary positive slack in the normalized rate. -/
theorem primeCertificate_eventually_exp_lower {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (L : ℕ) (hL : 0 < L) (B : ℝ → ℕ)
    (hcap : ∀ i ∈ s, 1 ≤ (L : ℝ) * (W i).lower)
    (hB : ∀ z, windowWeightSum s W z ≤ B z) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      exp ((finiteWindowRate s W L - η) * (L * N : ℕ)) ≤
        (primeCertificate L N B : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  let A : ℝ := ∑ i ∈ s, (W i).weight * (1 / (W i).lower - 1 / (W i).upper)
  have hnear : ∀ᶠ N : ℕ in atTop,
      A - (L : ℝ) * η <
        (∑ i ∈ s, (W i).weight * ∑ p ∈ (W i).primes N, log (p : ℝ)) / N :=
    (finite_window_log_sum_div_tendsto s W).eventually
      (lt_mem_nhds (show A - (L : ℝ) * η < A from sub_lt_self A (mul_pos hLR hη)))
  filter_upwards [hnear, eventually_finite_windows_large s W L,
    eventually_gt_atTop (0 : ℕ)] with N hnear hlarge hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmul := (le_div_iff₀ hNR).mp hnear.le
  have hlogs := finite_window_log_sum_le_log_certificate s W L N B hcap hlarge hB
  have hexponent : (finiteWindowRate s W L - η) * (L * N : ℕ) =
      (A - (L : ℝ) * η) * (N : ℝ) := by
    simp only [finiteWindowRate, Nat.cast_mul]
    dsimp [A]
    field_simp [hLR.ne']
    <;> ring
  calc
    exp ((finiteWindowRate s W L - η) * (L * N : ℕ)) ≤
        exp (log (primeCertificate L N B : ℝ)) :=
      Real.exp_le_exp.mpr (by rw [hexponent]; exact hmul.trans hlogs)
    _ = _ := Real.exp_log (by exact_mod_cast primeCertificate_pos L N B)

/-- Transfer the rate to any positive integer sequence containing the prime
certificate. In the construction the sequence is the actual common divisor. -/
theorem divisor_eventually_exp_lower {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (L : ℕ) (hL : 0 < L) (B : ℝ → ℕ)
    (hcap : ∀ i ∈ s, 1 ≤ (L : ℝ) * (W i).lower)
    (hB : ∀ z, windowWeightSum s W z ≤ B z)
    (D : ℕ → ℕ) (hDpos : ∀ N, 0 < D N)
    (hD : ∀ N, primeCertificate L N B ∣ D N) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      exp ((finiteWindowRate s W L - η) * (L * N : ℕ)) ≤ (D N : ℝ) := by
  filter_upwards [primeCertificate_eventually_exp_lower s W L hL B hcap hB hη]
    with N hN
  exact hN.trans (by exact_mod_cast Nat.le_of_dvd (hDpos N) (hD N))

end OddPiPowers.PrimeRates

end
