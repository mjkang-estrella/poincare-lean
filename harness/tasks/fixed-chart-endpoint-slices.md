# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/fixed-chart-endpoint-slices`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/fixed-chart-endpoint-slices_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/chain-parametrization-inventory.md` (the whole plan; your task is one of its
"First five bounded tasks" and is reproduced below verbatim), then the cited definitions.

# Task fixed-chart-endpoint-slices

### 3. `Poincare/Global/FixedChartEndpointSlices.lean`

A purely product-topology interface, independent of `g`. Inputs: `P : OpenPartialHomeomorph (E × E) (E × E)`, `A : Set E`, `hA : IsOpen A`, and

```lean
hfst : ∀ q ∈ P.source, (P q).1 = q.1
hzero : ∀ z ∈ A, (z, (0 : E)) ∈ P.source
hstationary : ∀ z ∈ A, P (z, 0) = (z, z)
```

Define `slice P hfst z : OpenPartialHomeomorph E E` with **exact** source `{v | (z,v) ∈ P.source}`, target `{y | (z,y) ∈ P.target}`, forward `fun v => (P (z,v)).2`, and inverse `fun y => (P.symm (z,y)).2`. Target `slice_zero` is `∀z∈A, slice P hfst z 0 = z`; target `slice_zero_mem_source` is `∀z∈A, 0 ∈ (slice P hfst z).source`. Prove `isOpen_slice_sourceLocus`, `isOpen_slice_targetLocus`, `continuousOn_slice_eval`, and `continuousOn_slice_symmEval` on their exact loci, restricting the first coordinate to `A`.

This closes the missing per-anchor partial-homeomorphism interface of the current product package; the inverse first-coordinate identity must be proved on `P.target` from `hfst` and `right_inv`. Gate: compile and probe `slice`, both zero laws, and all four joint-locus laws. Evidence: the product `endpoint` field and `endpoint_apply` of `FixedChartAnchorEndpointPackage`, plus `FixedChartUniformNormalRadius.F`. Stop if the exact source/target slice construction needs a stronger first-coordinate hypothesis; do not shrink by a fresh choice at each `z`.

