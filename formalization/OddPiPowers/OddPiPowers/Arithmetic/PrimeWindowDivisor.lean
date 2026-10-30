module

public import OddPiPowers.Arithmetic.PrimeWindowSums
public import OddPiPowers.Arithmetic.FiniteWindowCover

@[expose] public section

open scoped BigOperators
open Finset Real Filter

namespace OddPiPowers.PrimeRates

/-- The large-prime index set, independent of the auxiliary polynomial API. -/
def largePrimeIndices (L N : ℕ) : Finset ℕ :=
  (range (L * N + 1)).filter (fun p => p.Prime ∧ p ≤ L * N ∧ L * N < p * p)

noncomputable def primeCertificate (L N : ℕ) (B : ℝ → ℕ) : ℕ :=
  ∏ p ∈ largePrimeIndices L N, p ^ B ((N : ℝ) / (p : ℝ))

theorem primeCertificate_pos (L N : ℕ) (B : ℝ → ℕ) :
    0 < primeCertificate L N B := by
  classical
  exact Finset.prod_pos (fun p hp =>
    pow_pos (mem_filter.mp hp).2.1.pos _)

theorem log_primeCertificate (L N : ℕ) (B : ℝ → ℕ) :
    log (primeCertificate L N B : ℝ) =
      ∑ p ∈ largePrimeIndices L N, (B ((N : ℝ) / (p : ℝ)) : ℝ) * log (p : ℝ) := by
  classical
  simp only [primeCertificate, Nat.cast_prod, Nat.cast_pow]
  rw [Real.log_prod (fun p hp => pow_ne_zero _
    (by exact_mod_cast (mem_filter.mp hp).2.1.ne_zero))]
  simp only [Real.log_pow]

theorem PrimeWindow.primes_subset_large (W : PrimeWindow) (L N : ℕ)
    (hcap : 1 ≤ (L : ℝ) * W.lower)
    (hN : (L : ℝ) * W.upper ^ 2 < (N : ℝ)) :
    W.primes N ⊆ largePrimeIndices L N := by
  intro p hp
  obtain ⟨hpprime, hmem⟩ := (W.mem_primes N p).mp hp
  have hlarge := W.admissible_of_large L N p hcap hN hpprime.pos hmem
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), hpprime, hlarge⟩

/-- Extend each selected prime sum to a common index set and interchange the
two finite sums. The pointwise sum bound prevents double counting. -/
theorem finite_window_log_sum_le_log_certificate {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (L N : ℕ) (B : ℝ → ℕ)
    (hcap : ∀ i ∈ s, 1 ≤ (L : ℝ) * (W i).lower)
    (hN : ∀ i ∈ s, (L : ℝ) * (W i).upper ^ 2 < (N : ℝ))
    (hB : ∀ z, windowWeightSum s W z ≤ B z) :
    (∑ i ∈ s, (W i).weight * ∑ p ∈ (W i).primes N, log (p : ℝ)) ≤
      log (primeCertificate L N B : ℝ) := by
  classical
  have hext (i) (hi : i ∈ s) :
      ((W i).weight : ℝ) * ∑ p ∈ (W i).primes N, log (p : ℝ) =
        ∑ p ∈ largePrimeIndices L N,
          (if p ∈ (W i).primes N then ((W i).weight : ℝ) else 0) * log (p : ℝ) := by
    have hfilter : (largePrimeIndices L N).filter (fun p => p ∈ (W i).primes N) =
        (W i).primes N := by
      ext p
      simp only [mem_filter, and_iff_right_iff_imp]
      intro hp
      exact (W i).primes_subset_large L N (hcap i hi) (hN i hi) hp
    calc
      _ = ∑ p ∈ (W i).primes N, ((W i).weight : ℝ) * log (p : ℝ) := Finset.mul_sum _ _ _
      _ = ∑ p ∈ (largePrimeIndices L N).filter (fun p => p ∈ (W i).primes N),
          ((W i).weight : ℝ) * log (p : ℝ) := by rw [hfilter]
      _ = ∑ p ∈ largePrimeIndices L N,
          (if p ∈ (W i).primes N then ((W i).weight : ℝ) else 0) * log (p : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        split_ifs <;> simp
  rw [log_primeCertificate]
  calc
    _ = ∑ i ∈ s, ∑ p ∈ largePrimeIndices L N,
        (if p ∈ (W i).primes N then ((W i).weight : ℝ) else 0) * log (p : ℝ) :=
      Finset.sum_congr rfl hext
    _ = ∑ p ∈ largePrimeIndices L N,
        (∑ i ∈ s, if p ∈ (W i).primes N then ((W i).weight : ℝ) else 0) * log (p : ℝ) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := (mem_filter.mp hp).2.1
      have hlog : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
      apply mul_le_mul_of_nonneg_right _ hlog
      have hb := hB ((N : ℝ) / (p : ℝ))
      have hmem (i : ι) := (W i).mem_primes_quotient N p hprime
      simp only [windowWeightSum] at hb
      simp_rw [← hmem] at hb
      exact_mod_cast hb

theorem eventually_finite_windows_large {ι : Type*} (s : Finset ι)
    (W : ι → PrimeWindow) (L : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ i ∈ s, (L : ℝ) * (W i).upper ^ 2 < (N : ℝ) := by
  exact (Filter.eventually_all_finset s).mpr (fun i hi => (W i).eventually_large L)

end OddPiPowers.PrimeRates

end
