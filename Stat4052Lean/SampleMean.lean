/-
Copyright (c) 2026 Preston Perrill, Ani Vandrevu, Tonhy Park, Younus Ali. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Preston Perrill, Ani Vandrevu, Tonhy Park, Younus Ali
-/

import Mathlib

/-!
# The sample mean minimizes the sum of squared errors

For real observations `x₁, …, xₙ` with `n > 0`, the sample mean `x̄` satisfies
`∑ (xᵢ - x̄) ^ 2 ≤ ∑ (xᵢ - c) ^ 2` for every real `c`, with equality only at `c = x̄`.
The proof uses the decomposition `SSE(c) = SSE(x̄) + n (x̄ - c) ^ 2`.
-/

open Finset

/-- Sample mean of n real observations. -/
noncomputable def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Deviations from the sample mean sum to zero. -/
lemma sum_dev_mean_eq_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i - sampleMean x) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : (n : ℝ) * sampleMean x = ∑ i, x i := by
    unfold sampleMean
    field_simp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [h, sub_self]

/-- Decomposition: SSE(c) = SSE(mean) + n (mean - c) ^ 2. -/
lemma sse_decomp {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (x i - c) ^ 2 =
      ∑ i, (x i - sampleMean x) ^ 2 + n * (sampleMean x - c) ^ 2 := by
  have h0 := sum_dev_mean_eq_zero hn x
  calc ∑ i, (x i - c) ^ 2
      = ∑ i, ((x i - sampleMean x) ^ 2
          + 2 * (sampleMean x - c) * (x i - sampleMean x)
          + (sampleMean x - c) ^ 2) :=
        Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ i, (x i - sampleMean x) ^ 2
          + 2 * (sampleMean x - c) * ∑ i, (x i - sampleMean x)
          + ∑ _i : Fin n, (sampleMean x - c) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ i, (x i - sampleMean x) ^ 2 + n * (sampleMean x - c) ^ 2 := by
        rw [h0]
        simp

/-- Main theorem: the sample mean minimizes the sum of squared errors. -/
theorem sampleMean_minimizes_sse {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ i, (x i - sampleMean x) ^ 2 ≤ ∑ i, (x i - c) ^ 2 := by
  rw [sse_decomp hn x c]
  have : (0 : ℝ) ≤ n * (sampleMean x - c) ^ 2 := by positivity
  linarith

/-- The sample mean is the unique minimizer. -/
theorem sampleMean_unique_minimizer {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ)
    (h : ∑ i, (x i - c) ^ 2 = ∑ i, (x i - sampleMean x) ^ 2) :
    c = sampleMean x := by
  have hd := sse_decomp hn x c
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (n : ℝ) * (sampleMean x - c) ^ 2 = 0 := by linarith
  have h2 : (sampleMean x - c) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact absurd h' hn'
    · exact h'
  have h3 : sampleMean x - c = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
  linarith
