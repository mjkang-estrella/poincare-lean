# M3-predicates-11 blocked report

## Target

Task target: prove the raw constant model-vector tangent section

```lean
let s : ∀ y : M, TM y := fun y : M => (p : TM y)
MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% s) x
```

and then use it to obtain raw scalar metric entries

```lean
fun y : M => g.inner y p q
```

for fixed `p q : E`.

## Exact reduced goal

After the prescribed section reduction, the target becomes the differentiability
of the variable preferred-chart tangent coordinate change:

```lean
example (x : M) (p : E) :
    let s : ∀ y : M, TM y := fun y : M => (p : TM y)
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% s) x := by
  dsimp only
  rw [mdifferentiableAt_section]
  simp only [TangentBundle.trivializationAt_apply]
  change MDifferentiableAt I 𝓘(ℝ, E)
    (fun b : M => tangentCoordChange I b x b p) x
  exact (0 : ℕ)
```

Lean reports:

```text
<stdin>:29:2: error: Type mismatch
  0
has type
  ℕ
of sort `Type` but is expected to have type
  (MDiffAt fun b => (tangentCoordChange I b x b) p) x
of sort `Prop`
```

This is definitionally the same obstruction as in predicates-10:

```lean
fun b : M =>
  ((tangentBundleCore I M).coordChange (achart E b) (achart E x) b) p
```

## Why the requested core route does not close the goal

The relevant Mathlib field is fixed-index smoothness:

```lean
VectorBundleCore.contMDiffOn_coordChange
  (IB) [Z.IsContMDiff IB n] (i j : ι) :
  ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n
    (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j)
```

For the tangent bundle core this gives smoothness of

```lean
fun b => (tangentBundleCore I M).coordChange i j b
```

for fixed atlas indices `i` and `j`.  The reduced section goal has
`i = achart E b`, varying with the base point.  The core field therefore does
not apply to the needed function.

The theorem

```lean
mfderiv_chartAt_eq_tangentCoordChange
```

does identify

```lean
tangentCoordChange I b x b
```

with the manifold derivative of the fixed chart `chartAt E x` at `b`.  However,
Mathlib smooths this derivative in fixed tangent coordinates via
`ContMDiffAt.mfderiv_const`, i.e. through `inTangentCoordinates`; that
precomposes by `(trivializationAt E TM x).symmL` and gives the canonical
extension-section route already available as `mdifferentiableAt_extend`, not the
raw section `fun y => (p : TM y)`.

There is no local-constancy theorem for `b ↦ chartAt E b` in an arbitrary
`ChartedSpace`; the class only chooses a preferred chart containing each point.
So the target raw constant section is stronger than what the fixed-index bundle
core smoothness field supplies.

## Consequence

Deliverables 2 and 3 remain blocked, because raw metric entries

```lean
fun y : M => g.inner y p q
```

depend on the raw constant tangent sections.  The verified scalar-entry helper
from predicates-10 remains the canonical extension version:

```lean
ClosedSmoothRiemannianMetric.metric_pairing_extend_mdiffAt
```

which differentiates

```lean
fun y : M => g.inner y (extend E p y) (extend E q y)
```

at the chosen base point.

## Verification

No source declarations were added.  Run:

```bash
lake build Poincare.Global.ScalarVariation
```
