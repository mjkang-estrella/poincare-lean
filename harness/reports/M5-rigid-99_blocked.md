# M5-rigid-99 blocked: final assembly stops at endpoint equivalence witnesses

## Status

Added `Poincare/Global/LocalIsometryTheorem.lean`. No existing Lean files were
edited, including `Poincare.lean`.

The new module imports the public final-assembly chain and records the exact
assembly boundary. It deliberately states no curvature-only theorem and no
conditional wrapper, because the first unfed datum would otherwise be re-assumed
under a new name.

## First unfed witness

After unpacking
`UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors`,
the selector does provide, at the same common `T`, source and target
`linearizedEndpointCLM` maps together with strict derivatives and ray
identities. The final consumer
`BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`
does not consume those CLMs directly. It first requires continuous linear
equivalences whose coercions are exactly the selected endpoint CLMs:

```lean
{A B : E3 ≃L[ℝ] E3}
(hA :
  (A : E3 →L[ℝ] E3) =
    linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls)
(hB :
  (B : E3 →L[ℝ] E3) =
    linearizedEndpointCLM (Ψ := PsiT) T haddt hsmult)
```

The public selector exports:

```lean
HasStrictFDerivAt
  (expAtChartOpenPartialHomeomorph (g := g) x₀)
  (linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls) v
```

and the analogous target derivative, but it does not export `A`, `B`, `hA`, or
`hB`.

## Why this was not assumed

The available non-vacuous upgrade is
`CartanEquivUpgrade.exists_continuousLinearEquiv_of_sourceScaledNormalVector_action`.
It requires an explicit radial/transverse action equation for each endpoint
CLM:

```lean
∀ u : E3,
  linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls u =
    CartanLocalIsometry.sourceScaledNormalVector g x₀ ρ σ v u
```

and the corresponding target-side statement. Those action equations are not
among the public witnesses exported by the common-time selector. Assuming
`A`, `B`, `hA`, and `hB` in `LocalIsometryTheorem.lean` would therefore be a
vacuous wrapper around the missing upgrade, so the requested curvature-only
`cartanMap_isLocalIsometry` theorem is not stated.

## Verification

- Forbidden-token scan on `Poincare/Global/LocalIsometryTheorem.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/LocalIsometryTheorem.lean harness/reports/M5-rigid-99_blocked.md`
  - Result: success.
- `lake build Poincare.Global.LocalIsometryTheorem`
  - Result: success. The build replayed pre-existing imported-module warnings;
    no warning was emitted from `Poincare/Global/LocalIsometryTheorem.lean`.
  - Final lines:

```text
✔ [3206/3206] Built Poincare.Global.LocalIsometryTheorem (12s)
Build completed successfully (3206 jobs).
```
