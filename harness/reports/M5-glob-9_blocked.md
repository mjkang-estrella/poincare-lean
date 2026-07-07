# M5-glob-9 blocked report

## Delivered files

- `Poincare/Global/OffAnchorNaturality.lean`
- `harness/reports/M5-glob-9_blocked.md`

No existing Lean files or `Poincare.lean` were edited.

## Verified Lean payload

`OffAnchorNaturality.lean` imports `GeodesicPreservation` and adds one isolated
theorem:

- `Poincare.OffAnchorNaturality.carried_target_chart_exp_naturality_of_rigidStepCompatibleWith`

The theorem proves the strict off-anchor target-chart exponential naturality
identity for the carried old Cartan map, assuming the old germ has already been
re-centered to the explicitly aligned new-anchor Cartan germ on the common
strict source:

```lean
GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) (s.map x₁)
    (L₁
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x₁).symm ((chartAt E x₁) x))) =
  (chartAt E (s.map x₁)) (s.map x)
```

The proof uses the anchor-based naturality theorem from
`GeodesicPreservation.lean` for the re-anchored Cartan germ, then rewrites the
new germ value to the carried old value using
`InducedAlignment.CompatibleStep.RigidStepCompatibleWith`.

## Blocking boundary

The actual off-anchor re-centering theorem is still not available from the
current interfaces.  The theorem above consumes
`RigidStepCompatibleWith`, which is exactly the strict common-source `EqOn`
identifying the old carried germ with the new-anchor Cartan germ.

The reanchor thread has closed the first-order chart-transition derivative
bridge in `GeodesicReanchorClose.lean`, but the parked double-anchor ODE law
still needs the velocity-component Christoffel transition.  Without that
transition law, the geodesic-preservation route cannot produce the required
old-germ-versus-reanchored-germ `EqOn`.  The determinacy route is also still
same-anchor only: `GermDeterminacy.lean` can compare two `x₁`-anchored Cartan
germs after their tangent actions are identified, but it does not re-express
the old `s.germ` as an `x₁`-anchored germ.

## Verification

Command run:

```bash
lake build Poincare.Global.OffAnchorNaturality
```

Actual final result:

```text
✔ [3232/3232] Built Poincare.Global.OffAnchorNaturality (9.9s)
Build completed successfully (3232 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module uses
only completed Lean proofs and adds no `sorry`, new `axiom`, or `native_decide`.

