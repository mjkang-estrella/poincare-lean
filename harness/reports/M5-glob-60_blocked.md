# M5-glob-60 blocked: hosted third-variation CLM landed, endpoint continuity still missing

## Status

Verified partial progress was added in the required new Lean module:

- `Poincare/Global/HostedCLM.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds exactly one top-level theorem:

```lean
theorem Poincare.GeodesicTransport
  .chartChristoffel_hostedThirdVariation_endpoint_clm_of_linearODE_uniqueOn_Icc
```

This is the level-three analogue of
`secondVariation_endpoint_clm_of_linearODE_uniqueOn_Icc`.

Given a hosted third-variation solution family `Ω` for the linear ODE

```lean
η' = fderiv ℝ doubleF (ζ t) η
```

plus Picard-Lindelöf uniqueness data, initial values, closed-ball membership,
and the additivity/scalar-compatibility membership hypotheses, the theorem
constructs

```lean
D : (B × B) →L[ℝ] (B × B)
```

and proves both:

```lean
∀ η, D η = Ω η T
```

and the exact eventual endpoint package needed by `TransitionLands`:

```lean
∀ᶠ h in 𝓝 0,
  Ω h 0 = h ∧
    (∀ t ∈ Icc tmin tmax, HasDerivWithinAt (Ω h) ... (Icc tmin tmax) t) ∧
    Ω h T = D h
```

Linearity is proved by uniqueness of the linear ODE for `Ω (η + η')` versus
`Ω η + Ω η'`, and for `Ω (c • η)` versus `c • Ω η`.  Continuity of the endpoint
linear map is supplied by finite dimensionality via
`LinearMap.toContinuousLinearMap`.

## Remaining blocking boundary

The task's full target is still blocked at the endpoint-continuity package.
The landed theorem constructs the fixed-hosted-family endpoint CLM once the
global-in-perturbation uniqueness and membership hypotheses are supplied, but
the current exports still do not build the canonical neighborhood-indexed field

```lean
q ↦ D_q
```

for source and target endpoints.

The missing bridge is not a theorem-shape wrapper.  It still needs exported
uniform data that ties together:

1. hosted third-variation families and endpoint CLMs over a neighborhood of
   the base point `q`;
2. a uniform conversion of the `OmegaGronwall` bound into
   `ContinuousAt`/`ContinuousOn` for `q ↦ D_q`;
3. projection of the doubled endpoint CLM to the canonical source and target
   endpoint fields demanded by `EndpointContinuity.lean`:

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

Consequently the canonical endpoint-continuity packages and the unconditional
F-transition law were not assembled in this slice.

## Verification

Commands run:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/HostedCLM.lean
rg -n "^(structure|class|def|noncomputable def|theorem|lemma|axiom|abbrev) " Poincare/Global/HostedCLM.lean
git diff --check -- Poincare/Global/HostedCLM.lean
lake build Poincare.Global.HostedCLM
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
44:theorem chartChristoffel_hostedThirdVariation_endpoint_clm_of_linearODE_uniqueOn_Icc

git diff --check -- Poincare/Global/HostedCLM.lean
exit status 0

lake build Poincare.Global.HostedCLM
✔ [3247/3247] Built Poincare.Global.HostedCLM (3.2s)
Build completed successfully (3247 jobs).
```

The build replayed pre-existing imported-module warnings; no error remained in
`Poincare/Global/HostedCLM.lean`.
