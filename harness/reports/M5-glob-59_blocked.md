# M5-glob-59 blocked: local Ω residual lands, endpoint continuity still missing

## Status

Verified partial progress was added in the required new Lean module:

- `Poincare/Global/TransitionLands.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds three theorem-bearing steps:

```lean
theorem Poincare.flowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
```

This is the local/eventual form of the doubly residual Gronwall theorem.  It
replays the existing residual proof but requires the linearized family data and
the endpoint CLM representation only eventually near `h = 0`, matching the
shape of hosted local Picard-Lindelöf data.

```lean
theorem Poincare.GeodesicTransport
  .chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_eventually
```

This specializes the local/eventual residual theorem to the doubly-augmented
chart-Christoffel field.

```lean
theorem Poincare.GeodesicTransport
  .chartChristoffel_secondVariation_endpoint_hasFDerivAt_of_thirdVariation_eventually
```

This projects the paired endpoint derivative to the second-variation endpoint
field, giving the endpoint derivative once eventual third-variation endpoint
CLM data is available.

## Blocking boundary

The unconditional F-transition law still does not type from the current exports.
The first resistant shape is the endpoint-CLM package for the hosted
third-variation family.

The exported Ω existence theorem provides only local solution data:

```lean
∀ h : A × A, h ∈ closedBall (0 : A × A) r →
  Ω h 0 = h ∧
    (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Ω h) ... (Icc (-ε) ε) t) ∧
    ∀ t ∈ Icc (-ε) ε, Ω h t ∈ closedBall (0 : A × A) a
```

The landed local residual projection now needs the missing endpoint-CLM shape:

```lean
∀ᶠ h in 𝓝 (0 : A × A),
  Ω h 0 = h ∧
    (∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt (Ω h) ... (Icc (0 : ℝ) T) τ) ∧
    Ω h t = D h
```

No current exported theorem constructs this `D : (A × A) →L[ℝ] (A × A)` for the
hosted third-variation family.  The Grönwall endpoint bound in
`OmegaGronwall.lean` assumes such endpoint CLMs `D₁` and `D₂`; it does not
construct them.

After that, the bridge chain still needs the source and target canonical
endpoint-continuity data consumed by `EndpointContinuity`:

```lean
sourceU ∈ 𝓝 v
ContinuousOn sourceEndpoint sourceU
∀ q ∈ sourceU,
  HasFDerivAt (fun q' : E3 => fderiv ℝ eM q') (sourceEndpoint q) q

targetU ∈ 𝓝 (L v)
ContinuousOn targetEndpoint targetU
∀ q ∈ targetU,
  HasFDerivAt (fun q' : E3 => fderiv ℝ eS q') (targetEndpoint q) q
```

The current tower has the generic consumers for these fields, and now has a
local residual projection theorem, but it still lacks the exported projection
from the doubly-augmented `(A × A)` endpoint derivative/CLM to these
normal-vector-indexed canonical `E3` endpoint fields, plus their continuity.

## Verification

Commands run:

```bash
forbidden-token scan on Poincare/Global/TransitionLands.lean
top-level declaration scan on Poincare/Global/TransitionLands.lean
git diff --check -- Poincare/Global/TransitionLands.lean
lake build Poincare.Global.TransitionLands
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
35:theorem flowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
312:theorem chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_eventually
452:theorem chartChristoffel_secondVariation_endpoint_hasFDerivAt_of_thirdVariation_eventually

git diff --check -- Poincare/Global/TransitionLands.lean
exit status 0

lake build Poincare.Global.TransitionLands
✔ [3246/3246] Built Poincare.Global.TransitionLands (17s)
Build completed successfully (3246 jobs).
```

The build replayed pre-existing imported-module warnings; no error remained in
`Poincare/Global/TransitionLands.lean`.
