# M5-rigid-42 blocked: hosted linearized family local export

## Status

Blocked for the full local-isometry instantiation.  I added the new module
`Poincare/Global/LinearizedFamilyExport.lean` with one isolated, verified
statement exporting the concrete Picard-Lindelöf fixed-point family for the
hosted linearized geodesic equation on the PL closed ball.  I did not edit
existing Lean files, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.LinearizedFamilyExport.exists_hosted_linearized_solution_family_on_pl_closedBall
```

It takes PL data for the time-dependent linearized geodesic ODE along a hosted
base curve `γ`, chooses the actual PL flow of linearized states, and reindexes
that flow by endpoint directions via the strict-derivative datum
`((0 : E), T⁻¹ • w)`.  For every direction whose initial state lies in the PL
radius, the exported family satisfies:

```lean
Ψ w 0 = ((0 : E), T⁻¹ • w)
```

and solves

```lean
HasDerivWithinAt (Ψ w)
  (linearizedGeodesicFlowFieldAlong
    (GeodesicTransport.chartChristoffelField g x₀) γ t (Ψ w t))
  (Icc (-ε) ε) t
```

on the common interval, while remaining in the PL closed ball.

This is not a wrapper around an assumed family: the proof uses
`IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall`
to choose the concrete fixed-point flow.

## Remaining blocker

The strict-derivative consumer still needs a family over all endpoint
directions, with endpoint additivity and scalar homogeneity for all `w`.
The exported PL family is local in the initial-state closed ball.  The missing
next step is the rescaling/uniqueness argument that extends this local
linearized family globally in `w` and proves the endpoint additivity/smul
facts needed by `linearizedEndpointCLM`.

After that global family is available, the action-equation theorem still needs
the hosted radial derivative and the vector-valued rescaled-harmonic discharge
connected to this concrete family before the source/target `A`/`B` blocks and
`CartanScaleGeneric.cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings`
can be instantiated.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/LinearizedFamilyExport.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/LinearizedFamilyExport.lean
```

Actual result:

```text
41:theorem exists_hosted_linearized_solution_family_on_pl_closedBall
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/LinearizedFamilyExport.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.LinearizedFamilyExport
```

Actual result: succeeded, with pre-existing upstream warnings replayed.

Final build lines:

```text
Built Poincare.Global.LinearizedFamilyExport (13s)
Build completed successfully (3163 jobs).
```

