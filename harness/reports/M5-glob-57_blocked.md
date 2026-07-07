# M5-glob-57 blocked: endpoint-continuity bridge fires the C1 consumer

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/EndpointContinuity.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.EndpointContinuity
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_endpoint_continuity
```

It calls the existing `CanonicalC1` produced-field tower and replaces the
direct canonical assumptions

```lean
ContDiffAt ℝ 1 (fun q => fderiv ℝ eM q) v
ContDiffAt ℝ 1 (fun q => fderiv ℝ eS q) (L v)
```

by explicit endpoint-continuity data for source and target endpoint CLM fields:

```lean
sourceU ∈ 𝓝 v
ContinuousOn sourceEndpoint sourceU
∀ q ∈ sourceU,
  HasFDerivAt (fun q' => fderiv ℝ eM q') (sourceEndpoint q) q

targetU ∈ 𝓝 (L v)
ContinuousOn targetEndpoint targetU
∀ q ∈ targetU,
  HasFDerivAt (fun q' => fderiv ℝ eS q') (targetEndpoint q) q
```

The proof uses `contDiffAt_one_iff` to turn those local endpoint-continuity and
derivative-representation facts into the canonical `C1` inputs consumed by
`CanonicalC1`, then the existing bridge chain yields the signed Christoffel
F-transition law.

## Blocking boundary

This does not yet prove the requested unconditional F-transition law. The
remaining missing exported payload is still the analytic endpoint-dependence
layer:

1. instantiate the hosted third-variation family `Ω` from `ThirdFamily.lean` at
   the produced source and target datum used by the exponential-chart fields;
2. produce the endpoint CLM fields represented by those third-variation
   endpoints near each base point;
3. prove `ContinuousOn`/local continuity of those endpoint CLM fields, e.g. by
   the third-variation Gronwall dependence estimate.

Once those facts are exported in the shape consumed by this theorem, the
canonical `C1` bridge and F-transition consumer fire without further
`ContDiffAt` hypotheses.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/EndpointContinuity.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/EndpointContinuity.lean
git diff --check -- Poincare/Global/EndpointContinuity.lean
lake build Poincare.Global.EndpointContinuity
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
38:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_endpoint_continuity

git diff --check -- Poincare/Global/EndpointContinuity.lean
exit status 0

lake build Poincare.Global.EndpointContinuity
✔ [3238/3238] Built Poincare.Global.EndpointContinuity (14s)
Build completed successfully (3238 jobs).
```

The build replayed pre-existing imported-module warnings; no warning was
emitted from `Poincare/Global/EndpointContinuity.lean`.
