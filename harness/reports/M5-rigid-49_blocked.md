# M5-rigid-49 blocked: endpoint feed composed, hosted harmonic conversion still missing

## Status

Blocked for the requested unconditional `cartanMap_isLocalIsometry`-shaped
composition.  I added the new module
`Poincare/Global/CartanIsometryDone.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

## Verified payload

The new module proves:

```lean
Poincare.CartanIsometryDone.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique
```

This is the non-vacuous source action feed after M5-rigid-48: the theorem no
longer assumes the old rigid-47 `hendpoint` equality directly.  It derives
that equality by applying

```lean
Poincare.CartanEndpointUnique.hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc
```

and immediately feeds it into

```lean
Poincare.CartanActionEquations.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic
```

So the direct `hendpoint` blocker is genuinely removed at the source action
equation level.

## Remaining blocker

The full punctured normal-ball isometry still cannot be honestly composed from
the currently exported API.  The next missing bridge is the hosted conversion
showing that the time-rescaled harmonic state solves the same hosted
linearized chart-geodesic ODE along the cascade base curve.

Verbatim hypothesis:

```lean
(hΦderHosted : ∀ t ∈ Icc (-ε) ε,
  HasDerivWithinAt
    (fun τ : ℝ =>
      ((Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * τ)).1,
        speed •
          (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * τ)).2))
    (linearizedGeodesicFlowFieldAlong
      (GeodesicTransport.chartChristoffelField g x₀) γ t
      ((Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1,
        speed •
          (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).2))
    (Icc (-ε) ε) t)
```

I did not find an exported theorem deriving this from the constant-curvature
Jacobi oscillator, cutoff-one/unit/transverse hypotheses, and the cascade base
curve.  Assuming it in a final local-isometry theorem would restate the next
geometric bridge rather than composing the existing inventory.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanIsometryDone.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/CartanIsometryDone.lean
```

Actual result: success.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/CartanIsometryDone.lean
```

Actual result:

```text
42:theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique
```

Required build:

```bash
lake build Poincare.Global.CartanIsometryDone
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3162/3162] Built Poincare.Global.CartanIsometryDone (10s)
Build completed successfully (3162 jobs).
```
