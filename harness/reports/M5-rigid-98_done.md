# M5-rigid-98 done: uniform-flow five exported and aligned selector fires

## Status

Added `Poincare/Global/UniformFlowExport.lean`. No existing Lean files were
edited, including `Poincare.lean`.

The new module proves two non-vacuous exports:

- `UniformFlowExport.exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time`
- `UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors`

The single-side theorem replays the common-time hosted base construction while
keeping the underlying uniform-flow facts public. The common source/target
theorem then chooses the common time after the ball-uniform source and target
linearized PL margins are known, so it exports both:

```lean
T < εlin_source
T < εlin_target
```

For each side it exports the five hosted-flow fields on the uniform linearized
interval:

```lean
hα0
hαder
hαmem
hαtarget
hexp
```

These are threaded into
`IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow`.
For every endpoint direction in the final ball, the enriched selector now
returns source and target families with:

```lean
EnrichedCascade.LinearizedFamilyPackage g x₀ T εlin_source αs v Ψs
HasStrictFDerivAt
  (expAtChartOpenPartialHomeomorph (g := g) x₀)
  (linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls) v
(Ψs v T).1 =
  T • (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) T).2
```

and the analogous target fields:

```lean
EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀
  T εlin_target αt (align v) Ψt
HasStrictFDerivAt
  (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀)
  (linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult) (align v)
(Ψt (align v) T).1 =
  T • (αt (extChartAt I3 p₀ p₀, T⁻¹ • align v) T).2
```

## Scope note

This file closes the `M5-rigid-97` selector blocker: the uniform-flow facts are
public on the aligned PL intervals, and the source/target ray fields are
constructed by the enriched selector. It does not edit downstream assembly
modules or state a new curvature-only `cartanMap_isLocalIsometry` wrapper.

## Verification

- Forbidden-token scan on `Poincare/Global/UniformFlowExport.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/UniformFlowExport.lean`
  - Result: success.
- `lake build Poincare.Global.UniformFlowExport`
  - Result: success. The build replayed pre-existing imported-module warnings;
    no warning was emitted from `Poincare/Global/UniformFlowExport.lean`.
  - Final lines:

```text
✔ [3205/3205] Built Poincare.Global.UniformFlowExport (3.8s)
Build completed successfully (3205 jobs).
```
