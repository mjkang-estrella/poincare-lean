# M5-rigid-33 blocked: hosted scale is not accepted by the current bridge

## Files

- Added `Poincare/Global/CartanBlocksFinal.lean`.
- Added this report.
- Did not edit existing Lean modules or `Poincare.lean`.

## Blocked statement

```lean
theorem homogeneity_hosted_transverseScale_eq_bridge_transverseScale
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (δ : ℝ) (hδ : 0 < δ) {v : ClosedSmoothModel 3} (hvne : v ≠ 0) :
    let u := CartanHomogeneity.workingVelocity δ v
    let T := CartanHomogeneity.workingTime δ v
    let speed := Real.sqrt (CartanMap.sourceAnchorChartMetric g x₀ u u)
    Real.sin (speed * T) / (speed * T) =
      CartanLocalIsometry.transverseScale v
```

The requested assembly cannot be completed without this statement, or an
edited/generalized bridge, because `CartanCoefficientBridge` currently consumes
`CartanLocalIsometry.transverseScale v = sin ‖v‖ / ‖v‖` directly in its
transverse-transverse block, while the M5-rigid-33 task explicitly requires
using the honest `(u,T)` working-speed normalization and not forcing
`sin ‖v‖`.

## Verification

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/CartanBlocksFinal.lean
git diff --check -- Poincare/Global/CartanBlocksFinal.lean \
  harness/reports/M5-rigid-33_blocked.md
lake build Poincare.Global.CartanBlocksFinal
```

Actual result:

- forbidden-token scan found no matches;
- whitespace check succeeded;
- `lake build Poincare.Global.CartanBlocksFinal` succeeded with pre-existing
  upstream warnings replayed.

Final build lines:

```text
Built Poincare.Global.CartanBlocksFinal (13s)
Build completed successfully (3159 jobs).
```
