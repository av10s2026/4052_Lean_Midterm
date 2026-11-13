import Mathlib

open Finset

/-- Sample mean of n real observations. -/
noncomputable def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Deviations from the sample mean sum to zero. -/
lemma sum_dev_mean_eq_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i - sampleMean x) = 0 := by
  sorry

/-- Decomposition: SSE(c) = SSE(mean) + n(mean - c)^2. -/
lemma sse_decomp {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (x i - c)^2 = ∑ i, (x i - sampleMean x)^2 + n * (sampleMean x - c)^2 := by
  sorry

/-- Main theorem: the sample mean minimizes the sum of squared errors. -/
theorem sampleMean_minimizes_sse {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (x i - sampleMean x)^2 ≤ ∑ i, (x i - c)^2 := by
  sorry

/-- The sample mean is the unique minimizer. -/
theorem sampleMean_unique_minimizer {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ)
    (h : ∑ i, (x i - c)^2 = ∑ i, (x i - sampleMean x)^2) :
    c = sampleMean x := by
  sorry
