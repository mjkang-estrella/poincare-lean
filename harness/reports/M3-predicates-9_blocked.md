# M3-predicates-9 blocked report

## Target

Task target: prove the fixed-covector differentiability atom for the raise
field, in the shape consumed by `ScalarVariation`:

```lean
MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
  (T% (fun y : M => metricDualVectorAt g y φ)) x
```

The algebraic covector shape used by the current trace code is
`φ : Module.Dual ℝ (TM x)`, especially `φ = (Module.finBasis ℝ (TM x)).coord i`.

## What was mined

`Poincare/Global/Laplacian.lean` proves `ClosedSmoothRiemannianMetric.mdifferentiableAt_gradient`
by transporting the metric to a chart, blending the chart metric to a global
model metric `Ghat`, proving differentiability of the model field, pulling the
model field back, and then identifying it with the intrinsic gradient by metric
nondegeneracy.

For a fixed raw covector, the corresponding model field is not simply
`fun z => (Ghat z).inverse φ`.  If
`D z = mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm) (Set.range I) z`,
then the chart-side covector must be

```lean
fun z => φ.comp (D z).toLinearMap
```

so that pairing after chart pullback recovers `φ w`, not `φ (mfderiv chart y w)`.

## Blocker

The repo already has the relevant smoothness fact in tangent-coordinate form,
via `ContMDiffWithinAt.mfderivWithin_const`, and also has smoothness of inverse
chart tangent fields through
`CovariantDerivative.contMDiffOn_inverseChart_tangentMap`.

The missing bridge is a reusable theorem converting the tangent-coordinate
smoothness of the inverse-chart derivative into smoothness of the raw map

```lean
fun z =>
  mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm) (Set.range I) z
```

as an `E ->L[ℝ] E` valued function, or equivalently a theorem smooth enough to
build `fun z => φ.comp (D z).toLinearMap` as a continuous/model covector family.

Without that bridge, the `mdifferentiableAt_gradient` proof cannot be
specialized by replacing `df` with a constant covector: the fixed raw covector
still varies in chart coordinates through `D z`.

## Exact failing Lean goal state

```text
<stdin>:31:8: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
<stdin>:33:12: error: typeclass instance problem is stuck
  ContinuousSMul ?m.265 ?m.266

Note: Lean will not try to resolve this typeclass instance problem because the first, second, third, fourth, and fifth type arguments to `ContinuousSMul` contain metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
<stdin>:35:2: error: Type mismatch: After simplification, term
  hD
 has type
  ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1
    (inTangentCoordinates 𝓘(ℝ, E) I id (↑(chartAt E x).symm) (mfderiv% ↑(chartAt E x).symm) (↑(chartAt E x) x)) univ
    (↑(chartAt E x) x)
but is expected to have type
  ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1 (fun z => mfderiv% ↑(chartAt E x).symm z) univ (↑(chartAt E x) x)
n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
x : M
htarget : ↑(extChartAt I x) x ∈ (extChartAt I x).target
hsmWithin : ContMDiffWithinAt 𝓘(ℝ, E) I 2 (↑(extChartAt I x).symm) (range ↑I) (↑(extChartAt I x) x)
hD :
  ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1
    (inTangentCoordinates 𝓘(ℝ, E) I id (↑(extChartAt I x).symm)
      (mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I x).symm) (range ↑I)) (↑(extChartAt I x) x))
    (range ↑I) (↑(extChartAt I x) x)
⊢ ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1
    (fun z =>
      have this := mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I x).symm) (range ↑I) z;
      this)
    (range ↑I) (↑(extChartAt I x) x)
```

## Verification

No Lean source files were changed.  `lake build Poincare.Global.ScalarVariation`
was rerun after adding this report and completed successfully.
