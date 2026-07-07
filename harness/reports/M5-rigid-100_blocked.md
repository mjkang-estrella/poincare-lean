# M5-rigid-100 blocked: pairing upgrade proved, exported pairing pullbacks still missing

## Status

Added `Poincare/Global/PairingUpgrade.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The new module proves the pairing-based linear algebra upgrade requested in
this task: a continuous linear endpoint map whose pullback pairing is
positive-definite has trivial kernel, hence upgrades to a continuous linear
equivalence on the finite-dimensional model space.  The proof uses the
positive-definiteness lemmas already exposed by `CartanMap.lean`.

## Verified payload

The new module exports:

```lean
Poincare.PairingUpgrade.injective_of_pullback_posDef
Poincare.PairingUpgrade.exists_continuousLinearEquiv_of_pullback_posDef
Poincare.PairingUpgrade.exists_continuousLinearEquiv_of_sourceAnchor_pullback
Poincare.PairingUpgrade.exists_continuousLinearEquiv_of_targetAnchor_pullback
Poincare.PairingUpgrade.exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_pullback
Poincare.PairingUpgrade.exists_continuousLinearEquiv_of_target_linearizedEndpointCLM_pullback
Poincare.PairingUpgrade.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_hosted_anchor_pullbacks
```

The hosted CLM upgrades construct `A` and `B` with the exact downstream
coercion equalities:

```lean
(A : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls
(B : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult
```

The final adapter then feeds these into
`PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed`
and produces the Cartan strict derivative plus chart-metric pullback identity.

## Remaining blocker

The curvature-only assembly still cannot be stated without re-assuming the
first unfed pairing-pullback facts.  After the public common-time selector
exports `Ψs`, `Ψt`, `hadds`, `hsmuls`, `haddt`, `hsmult`, and the strict
derivatives with the selected `linearizedEndpointCLM`s, the new upgrade needs
the following non-vacuous source and target pullback identities:

```lean
(hSourcePullback :
  ∀ a a' : E,
    CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        (Ψs a T).1 (Ψs a' T).1 =
      CartanMap.sourceAnchorChartMetric g x₀ a a')

(hTargetPullback :
  ∀ b b' : E,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (Ψt b T).1 (Ψt b' T).1 =
      CartanMap.targetAnchorChartMetric p₀ b b')
```

These are exactly the positive-definite pullback facts that make the selected
CLMs invertible.  They are not exported by
`UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors`.
Assuming them inside a curvature-only theorem would just rename the remaining
pairing feed, so no curvature-only `cartanMap_isLocalIsometry` wrapper is
stated.

## Verification

- Forbidden-token scan on `Poincare/Global/PairingUpgrade.lean`
  - Result: no matches.
- `lake build Poincare.Global.PairingUpgrade`
  - Result: success.  The build replayed pre-existing upstream warnings; no
    new error was emitted from `Poincare/Global/PairingUpgrade.lean`.
  - Final lines:

```text
✔ [3155/3155] Built Poincare.Global.PairingUpgrade (3.2s)
Build completed successfully (3155 jobs).
```
