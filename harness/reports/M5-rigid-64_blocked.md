# M5-rigid-64 blocked: interval/germ helpers added, unit-speed package field still missing

## Status

Added `Poincare/Global/IsometryInstantiate.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module proves small, non-vacuous helper facts needed by the intended
instantiation path:

```lean
Poincare.IsometryInstantiate.cutoffOneLocus
Poincare.IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor
Poincare.IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
Poincare.IsometryInstantiate.hasDerivAt_of_hasDerivWithinAt_larger_Icc
Poincare.IsometryInstantiate.hasDerivAt_on_Icc_of_hasDerivWithinAt_on_larger_Icc
Poincare.IsometryInstantiate.geodesicFlow_hasDerivAt_on_shrunk_Icc
Poincare.IsometryInstantiate.linearizedFlow_hasDerivAt_on_shrunk_Icc
```

These discharge two mechanical interval-shrinking needs that appear when one
tries to instantiate `SourcePackage`/`TargetPackage` on actual hosted cascade
data:

* package the cutoff-one germ as an explicit `cutoffOneLocus` membership;
* upgrade `HasDerivWithinAt` on a larger interval to `HasDerivAt` on a
  strictly smaller `Icc`.

## Blocker

The requested final theorem was not added.  The source and target rescaled
feeds still cannot be produced from the currently exported hosted/cascade data
without an additional interval/norm package theorem.

The first resistant package field is the unit-speed hypothesis in
`SourcePackage.source_hosted_rescaled_endpoint_pairing_eq_pinned_of_interval_norm_package`:

```lean
(hunit : ∀ s ∈ Icc tmin tmax,
  CovariantDerivative.chartMetric g.inner x₀
    (γ s).1 (γ s).2 (γ s).2 = 1)
```

The target supplier has the same field specialized to the round sphere:

```lean
(hunit : ∀ s ∈ Icc tmin tmax,
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
    (γ s).1 (γ s).2 (γ s).2 = 1)
```

`CartanCascade.exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl`
exports chart-source membership, endpoint linearized families, endpoint
additivity/homogeneity, and strict derivatives.  It does not export unit-speed
facts for the base curves
`αs (extChartAt I x₀ x₀, Ts⁻¹ • v)` or
`αt (extChartAt I p₀ p₀, Tt⁻¹ • align v)`.

`CartanHomogeneity.exists_shrunk_cutoff_one_homogeneity_conversion` also does
not supply this field.  Its purpose is explicitly non-unit-speed hosting, and
the available normalization in `SourcePackage.norm_workingVelocity_eq_half`
gives

```lean
‖CartanHomogeneity.workingVelocity δ v‖ = δ / 2
```

not the transported chart-metric identity required by `hunit`.  Thus applying
the existing source/target suppliers at the actual hosted data would still
leave the displayed `hunit` field as a real mathematical obligation, not a
pairing hypothesis and not a scalar bookkeeping issue.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/IsometryInstantiate.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/IsometryInstantiate.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.IsometryInstantiate
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module emitted no local warnings after the final cleanup.

Final build lines:

```text
✔ [3178/3178] Built Poincare.Global.IsometryInstantiate (1.9s)
Build completed successfully (3178 jobs).
```
