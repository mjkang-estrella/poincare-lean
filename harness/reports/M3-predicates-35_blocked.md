# M3-predicates-35 blocked report

## Summary

Two bridge checkpoints were proved and committed:

- `f1cfa177`:
  `Poincare.ClosedSmoothRiemannianMetric.contDiff_three_blendedChartMetric`.
  This packages the existing `CovariantDerivative.contDiff_blendedChartMetric`
  machinery as the required `C^3` regularity for the blended chart
  representative
  `CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀`.
- `e9023ba6`:
  `Poincare.ClosedSmoothRiemannianMetric.chartTransportedLeviCivitaValueAt_eq_leviCivita_of_eventually_eq_one`.
  This restates the goal-1 transport theorem against the public
  `g.leviCivita` connection rather than the internal
  `LeviCivitaExistence.closedLeviCivitaConnection g`.

The Ricci-divergence and exterior-derivative bridges were not proved.

## Pivot checkpoint

The intended bridge 3 has the shape:

```lean
tensorDivergenceOneFormAt g (ricciVariationField g)
    ((extChartAt I x₀).symm z) w
  =
RicciFlow.RicciFlow.ricciDivergence Ghat z w_chart
```

where
`Ghat = CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀`, and
`w_chart` is the chart-coordinate representative of `w`.

Unfolding the closed side gives:

```lean
∑ i,
  covTensor2DerivAt g (ricciVariationField g) y
    (metricDualVectorAt g y ((Module.finBasis ℝ (TM y)).coord i))
    ((Module.finBasis ℝ (TM y)) i) w
```

and

```lean
covTensor2DerivAt g (ricciVariationField g) y v p q
  =
extDerivFun
    (fun y' : M =>
      g.ricciAt y' (extend E p y') (extend E q y')) y v
  - g.ricciAt y (g.leviCivita (extend E p) y v) q
  - g.ricciAt y p (g.leviCivita (extend E q) y v)
```

Unfolding the model side gives:

```lean
∑ k,
  RicciFlow.RicciFlow.covRicciDeriv Ghat z
    ((Ghat z).inverse
      (LinearMap.toContinuousLinearMap
        ((Module.finBasis ℝ E).coord k)))
    w_chart ((Module.finBasis ℝ E) k)
```

The model tensor-divergence bridge already exists internally as
`RicciFlow.RicciFlow.tensorDivOneForm_coordRicciForm`, but it applies after
the model object is already `coordRicciForm Ghat`. The closed side still has
the derivative term

```lean
extDerivFun
  (fun y' : M =>
    g.ricciAt y' (extend E p y') (extend E q y')) y v
```

which is not definitionally comparable with

```lean
(fderiv ℝ (fun z' : E => RicciFlow.RicciFlow.coordRicciForm Ghat z' ...) z
  v_chart) p_chart q_chart
```

without a new derivative-level chart bridge for the Ricci field.

The connection-level bridge proved in goal 1, and wrapped here as
`chartTransportedLeviCivitaValueAt_eq_leviCivita_of_eventually_eq_one`,
does identify the Christoffel correction terms. It does not identify the
`extDerivFun` of the closed Ricci field through the canonical `extend E`
sections. The historical raw-frame/section differentiability obstruction
therefore reappears at bridge 3.

## Missing bridge surface

Searches found no existing theorem transporting closed Ricci/scalar curvature
to model chart expressions:

- No closed-to-model Ricci bridge of the form
  `g.ricciAt ((extChartAt I x₀).symm z) p q =
   RicciFlow.RicciFlow.coordRicci Ghat z p_chart q_chart`.
- No scalar bridge
  `g.scalarAt ((extChartAt I x₀).symm z) =
   RicciFlow.RicciFlow.coordScalar Ghat z`.
- No derivative bridge for
  `fun y' => g.ricciAt y' (extend E p y') (extend E q y')`.
- No derivative bridge for
  `fun y' => g.scalarAt y'` to
  `fun z' => RicciFlow.RicciFlow.coordScalar Ghat z'`.

The closest existing closed theorem is
`ricciAt_eq_curvature_contraction`, which rewrites `g.ricciAt` as a trace of
`CovariantDerivative.curvatureOp g.leviCivita` on canonical extensions. That
is still an intrinsic curvature expression, not a chart/model expression.

## Pivot decision

The bridge route should not be continued by adding assumed Ricci/scalar
transport statements. Curvature is tensorial pointwise, but the required
bridge 3 is a first derivative of Ricci in closed coordinates, so the raw
`extend E` section differentiability pathology is still present.

The native route should replay the model second-Bianchi computation in the
closed extend-frame vocabulary:

1. Use the predicates-26..31 first- and second-derivative toolkit around
   `covTensor2DerivAt`, `covTensor2SecondDerivAt`, and the existing
   extend-frame Hessian/trace lemmas.
2. Prove the closed first contracted Bianchi identity directly from
   `CovariantDerivative.curvatureOp g.leviCivita`, torsion-freeness, and the
   closed connection regularity instance.
3. Contract against `metricDualVectorAt g y` and the finite tangent basis to
   get `ClosedContractedBianchiOneFormAt g y`.
4. Feed the result through `ClosedContractedBianchiAt.of_oneForm_near`.

That native route was not completed in this session.

## Exact remaining goal

The remaining target is still:

```lean
∀ᶠ y in nhds x, ClosedContractedBianchiOneFormAt g y
```

unfolding to:

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    (1 / 2 : ℝ) * extDerivFun (fun z : M => g.scalarAt z) y w
```

Once this is available, the existing reducer remains:

```lean
ClosedContractedBianchiAt.of_oneForm_near
```

The final `ClosedContractedBianchiAt` and Hamilton scalar evolution theorem
were not discharged.

## Verification

After the two theorem commits:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success, with existing linter warnings, ending with:

```text
Build completed successfully (2806 jobs).
```

Forbidden-placeholder scan on the edited Lean file:

```bash
rg -n "<forbidden-placeholder-pattern>" Poincare/Global/ScalarVariation.lean
```

Result: no matches.

Whitespace check:

```bash
git diff --check
```

Result: success.
