# The Sample Mean Minimizes Squared Error: A Lean 4 Formalization

STAT 4052, Fall 2026 · Midterm Lean 4 Project
Authors: Preston Perrill, Ani Vandrevu, Tony Park, Younus Ali

**Submitted version:** release `v1.0-submission`

## Goal
Formally verify, in Lean 4 with Mathlib, that the sample mean is the unique
minimizer of the sum of squared errors.

## Main result
Let n ≥ 1 and x₁, …, xₙ ∈ ℝ. Define the sample mean x̄ = (1/n) ∑ᵢ xᵢ and
SSE(c) = ∑ᵢ (xᵢ − c)². Then

1. SSE(x̄) ≤ SSE(c) for every c ∈ ℝ, and
2. if SSE(c) = SSE(x̄), then c = x̄.

The proof rests on the decomposition SSE(c) = SSE(x̄) + n(x̄ − c)².

## External inputs
No additional external axioms are used beyond the stated theorem hypotheses
and the standard Lean/mathlib foundations.
`#print axioms sampleMean_unique_minimizer` reports only `propext`,
`Classical.choice`, and `Quot.sound` (Lean's standard foundations).

## What is verified
Lean checks results 1 and 2 above for any n real observations with
n ≥ 1. Nothing is assumed beyond these hypotheses. The development contains
no `sorry` or `admit`.

## Main files and theorem names
All results are in `Stat4052Lean/SampleMean.lean`.

| Lean name | Statement |
|---|---|
| `sampleMean` | Definition: x̄ = (∑ xᵢ) / n |
| `sum_dev_mean_eq_zero` | ∑ (xᵢ − x̄) = 0 |
| `sse_decomp` | SSE(c) = SSE(x̄) + n(x̄ − c)² |
| `sampleMean_minimizes_sse` | **Main theorem:** SSE(x̄) ≤ SSE(c) for all c |
| `sampleMean_unique_minimizer` | SSE(c) = SSE(x̄) implies c = x̄ |

Other files: `Stat4052Lean.lean` (root import file), `lakefile.toml`
(build configuration), `lean-toolchain` (pinned Lean version),
`lake-manifest.json` (pinned Mathlib version).

## Build instructions
Requires `git` and [elan](https://github.com/leanprover/elan). Elan
automatically installs the Lean version pinned in `lean-toolchain`.

    git clone https://github.com/av10s2026/4052_Lean_Midterm.git
    cd 4052_Lean_Midterm
    git checkout v1.0-submission
    lake exe cache get
    lake build

`lake exe cache get` downloads precompiled Mathlib (a few minutes). Without
it, Mathlib compiles from source (several hours).

A successful build ends with `Build completed successfully`. To confirm there
are no proof placeholders:

    grep -rn "sorry\|admit" Stat4052Lean/

This command should print nothing.
