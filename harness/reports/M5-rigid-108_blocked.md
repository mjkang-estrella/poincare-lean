# M5-rigid-108 blocked: coefficient-time tuple constructor proved, selector data still not exported

## Outcome

Added `Poincare/Global/CoefficientShrink.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The new module proves the non-vacuous arithmetic shrink needed after
`M5-rigid-107`: if the scalar norm-system coefficient has a ball-uniform bound
`‖Aop‖ ≤ C`, the selector time has been shrunk to

```lean
C * T ≤ (1 : ℝ) / 2
```

and the moving quadratic centers are uniformly bounded by `Q`, then the module
constructs concrete bounded Picard-Lindelöf tuple parameters
`radius rNorm LNorm KNorm B` and proves the side conditions, including the
verbatim bound

```lean
‖Aop‖ * T ≤ 1
```

Main declarations:

```lean
Poincare.CoefficientShrink.exists_radius_tuple_of_uniform_center_bound
Poincare.CoefficientShrink.source_exists_radius_tuple_of_uniform_center_bound
Poincare.CoefficientShrink.target_exists_radius_tuple_of_uniform_center_bound
Poincare.CoefficientShrink.source_transverseTransverse_of_selector_coefficient_shrink
Poincare.CoefficientShrink.target_transverseTransverse_of_selector_coefficient_shrink
```

The source/target transverse declarations feed the constructed tuple into the
existing `TransverseExport` bounded-data adapters.  The remaining Gronwall and
speed-pinned membership bounds are kept as explicit hypotheses on the
constructed radius, matching the downstream `ScalarPin`/`GronwallMembership`
interface.

## Remaining blocker

The curvature-only selector still does not export the actual hypotheses needed
to instantiate this constructor:

```lean
‖Aop‖ ≤ C
∀ w ∈ closedBall (0 : E3) (R : ℝ), ‖center w‖ ≤ Q
C * T ≤ (1 : ℝ) / 2
```

In particular, the current public selector/transverse API still exposes bounded
norm-system data as caller-supplied side conditions.  This file removes the
radius-tuple arithmetic obstruction once a ball-uniform coefficient bound and
coefficient-time shrink are available, but it does not prove that bound from
the selector's compact tube or thread a curvature-only theorem through
`BlockDiagonal` without those exported data.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/CoefficientShrink.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/CoefficientShrink.lean`
  - Result: success.
- `lake build Poincare.Global.CoefficientShrink`
  - Result: success.  The build replayed pre-existing imported-module warnings
    and emitted local unused-variable warnings for existential tuple components
    in the two continuation theorem statements.
  - Final lines:

```text
⚠ [3210/3210] Built Poincare.Global.CoefficientShrink (2.8s)
Build completed successfully (3210 jobs).
```
