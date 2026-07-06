# M5-bridge-2 blocked

## Scope

Added `Poincare/Global/ChartCurvatureBridge2.lean`.  No existing Lean source
file and no root import file was edited.

The full manifold-level chart bridge is not closed in this strict partial.
The completed step is the requested packaging against the plain family
`GeodesicTransport.chartChristoffelField g x₀`.

## Proved packaging bridge

```lean
theorem Poincare.ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature
```

Statement shape:

```lean
chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀)
    (extChartAt I x₀ x₀) u v w
=
CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
  (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
    F (x := extChartAt I x₀ x₀) u)
  (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
    F (x := extChartAt I x₀ x₀) v)
  (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
    F (x := extChartAt I x₀ x₀) w)
  (extChartAt I x₀ x₀)
```

Here `F = ClosedSmoothModel n` and `I = closedSmoothModelWithCorners n`.
The explicit `E := fun x : F => TangentSpace 𝓘(ℝ, F) x` annotation is
essential: otherwise `FiberBundle.extend` can elaborate as the trivial
`F`-bundle extension rather than the model tangent-bundle extension.  The
identification used is the model equality
`TangentSpace 𝓘(ℝ, F) z = F`.

The proof uses:

- M5-bridge-1's swapped expansion
  `chartCurvatureOf_eq_fderiv_apply_swapped_of_eventually_symm`.
- `eventually_christoffelOneForm_symm` for the inner slot swaps.
- `CovariantDerivative.curvatureOp_modelLeviCivita_extend`.
- `CovariantDerivative.christoffelAt_symm` for the outer one-form/model
  slot convention swap.

## Remaining blocker

The missing final bridge is now sharply isolated as a curvature-level chart
transport theorem:

```lean
mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) x₀
  (CovariantDerivative.curvatureOp g.leviCivita
    (extend F u) (extend F v) (extend F w) x₀)
=
CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
  (extend_model_at_anchor (mfderiv% (extChartAt I x₀) x₀ u))
  (extend_model_at_anchor (mfderiv% (extChartAt I x₀) x₀ v))
  (extend_model_at_anchor (mfderiv% (extChartAt I x₀) x₀ w))
  (extChartAt I x₀ x₀)
```

The repo has the ingredients for this but not the assembled curvature theorem:

- `chartLeviCivita_eventuallyEq_closed` gives germ agreement of each
  transported Levi-Civita hom with `g.leviCivita`.
- `chartTransportedLeviCivitaHom_inCoordinates_apply_chart` identifies one
  transported connection application in chart coordinates.
- `chartTransportedLeviCivitaSection_extend_apply_chart` shows canonical
  manifold extensions have constant model representatives in the anchor chart.
- `mlieBracket_extend_extend_eventually_eq_zero` handles the bracket term for
  canonical extensions.

What is still missing is the non-vacuous curvature-level assembly combining
these four value-level facts across both iterated connection terms and the
bracket term, analogous in spirit to
`ClosedSmoothRiemannianMetric.constSMul_curvatureOp_extend_apply` but with an
extra chart pushforward/pullback layer.

## Sphere assembly status

The sphere witness should follow after that transport theorem by chaining:

1. this packaging lemma,
2. `roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel`,
3. `conformalChartMetric_chartCurvatureOf_sphereChristoffel`,
4. `roundSphereMetric3_inner_chartAt_symm_eq`.

I did not add a sphere wrapper because the manifold curvature pushforward is
still absent.

## Verification

Command run:

```bash
lake build Poincare.Global.ChartCurvatureBridge2
```

Result: success.  The build completed `Poincare.Global.ChartCurvatureBridge2`
and replayed existing upstream linter warnings; there were no errors from the
new module.
