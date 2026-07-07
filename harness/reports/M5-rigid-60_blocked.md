# M5-rigid-60 blocked: cascade-pairing bridge verified, exact pinned feed still missing

## Status

Added `Poincare/Global/CascadePinned.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module proves the non-vacuous upstream bridge that the existing
theorems did not expose in cascade-friendly shape:

```lean
Poincare.CascadePinned.actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc
Poincare.CascadePinned.chartMetric_pairing_eq_pinned_of_blended_pairing
Poincare.CascadePinned.hosted_rescaled_endpoint_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc
```

The first theorem is the polarized Jacobi pairing theorem with
`HasDerivWithinAt` hypotheses, matching the derivative shape exported by the
hosted cascade.  The second theorem converts the resulting blended
`chartGeodesicMetric` formula to the genuine transported chart metric under
the endpoint cutoff-one equality.  The third theorem packages these for the
cascade initial-data shape

```lean
∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w)
```

and proves the honest rescaled endpoint formula

```lean
∀ w w' : E,
  CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
      (Ψ w T).1 (Ψ w' T).1 =
    Real.sin T ^ 2 *
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w')
```

assuming the corresponding quadratic `normA` identities and cutoff/endpoint
identification.

## Remaining blocker

This is not yet the exact pinned feed consumed by `EqualityChain.lean`.  The
consumer still needs the unscaled hosted formulas:

```lean
∀ a a' : E,
  CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
      (Ψs a Ts).1 (Ψs a' Ts).1 =
    Real.sin θs ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a'
```

and

```lean
∀ a a' : E,
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v))
      (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
    Real.sin θt ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')
```

The first concrete missing sub-hypothesis, if one tries to feed the new
rescaled theorem directly, is the family-level quadratic identity:

```lean
∀ w : E,
  JacobiNormSystem.normA g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ w τ).1) T =
    Real.sin T ^ 2 *
      GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)
```

`CartanCascade.lean` exports the rescaled initial data, within-interval
linearized ODE, endpoint additivity/homogeneity, and strict derivative data.
It does not export the remaining hypotheses needed to derive the displayed
quadratic identities from
`CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc`:
the base geodesic `HasDerivAt` shape, unit-speed hypothesis, orthogonality
hypothesis, cutoff-one germ along the interval, norm-system closed-ball
membership, and the norm-system initial values.  The target side has the same
gap after specializing to `roundSphereMetric3`; the curvature witness is
available, but these interval/norm hypotheses are still not packaged for the
actual target cascade.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CascadePinned.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/CascadePinned.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CascadePinned
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module emitted no warnings after removing an unused section variable.

Final build lines:

```text
✔ [3173/3173] Built Poincare.Global.CascadePinned (2.6s)
Build completed successfully (3173 jobs).
```
