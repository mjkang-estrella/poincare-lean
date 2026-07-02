# M3-predicates-10 blocked report

## Target

Task target: prove the fixed-covector differentiability atom

```lean
MDifferentiableAt I 𝓘(ℝ, E)
  (fun y : M => metricDualVectorAt g y φ) x
```

for a fixed covector `φ`, using the scalar-entry / dual-basis route and without
`mfderiv` of `extChartAt.symm`, charts, or `inTangentCoordinates`.

## Verified progress

`Poincare/Global/ScalarVariation.lean` now contains three reusable proved
helpers:

```lean
ClosedSmoothRiemannianMetric.mdifferentiableAt_clm_of_apply
ClosedSmoothRiemannianMetric.mdifferentiableAt_clm_dual_of_apply
ClosedSmoothRiemannianMetric.metric_pairing_extend_mdiffAt
```

The first two port the model-space finite-dimensional CLM reconstruction
pattern to manifold-domain `MDifferentiableAt` targets.  The third records the
scalar metric-entry fact that is directly available from
`ClosedSmoothRiemannianMetric.metric_pairing_mdiffAt` and canonical extension
sections.

## Blocker

The requested step 1 needs raw scalar entries

```lean
fun y : M => g.inner y p q
```

with fixed raw model vectors `p q : E`.  That does typecheck because
`TangentSpace I y` is definitionally the model vector type, but proving it from
the smooth Riemannian metric is not the same as using the canonical extension
sections.  The raw constant tangent field

```lean
let s : ∀ y : M, TM y := fun y => (p : TM y)
T% s
```

is not discharged by `mdifferentiableAt_extend`; after reducing section
differentiability it requires differentiability of the moving preferred-chart
tangent coordinate expression.  That is exactly the chart-coordinate route the
task forbids.

The available verified scalar-entry lemma is instead

```lean
fun y : M => g.inner y (extend E p y) (extend E q y)
```

for fixed `p q : TM x`.  This is not definitionally the raw entry
`g.inner y p q` away from `x`, so it does not reconstruct the raw metric CLM
whose inverse is used by `metricDualVectorAt g y φ`.

## Exact failing Lean goal state

The smallest failed subgoal is raw constant tangent-field differentiability:

```lean
example (x : M) (p : E) :
    let s : ∀ y : M, TM y := fun y : M ↦ (p : TM y)
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% s) x := by
  dsimp only
  rw [mdifferentiableAt_section]
  simp only [TangentBundle.trivializationAt_apply]
  exact (0 : ℕ)
```

Lean reports:

```text
<stdin>:25:2: error: Type mismatch
  0
has type
  ℕ
of sort `Type` but is expected to have type
  (MDiffAt fun b =>
      (fderivWithin ℝ (↑((chartAt E x).extend I) ∘ ↑((chartAt E b).extend I).symm) (Set.range ↑I)
          (↑((chartAt E b).extend I) b))
        p)
    x
of sort `Prop`
```

So the scalar-entry route is blocked before the inverse-map step: raw constant
model-vector entries force a chart/`fderivWithin` coordinate-change obligation.

## Verification

The final module build in this run succeeded:

```bash
lake build Poincare.Global.ScalarVariation
```

Result:

```text
Build completed successfully (2805 jobs).
```
