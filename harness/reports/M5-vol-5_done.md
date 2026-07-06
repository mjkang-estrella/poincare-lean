# M5-vol-5: done

Task: Goal 10, total and mean scalar curvature.

## Delivered

Added `Poincare/Global/ScalarIntegral.lean`.

Public continuity and integrability signatures:

```lean
theorem scalarAt_continuous (g : ClosedSmoothRiemannianMetric n M) :
    Continuous (fun x : M ↦ g.scalarAt x)

theorem scalarAt_integrable (g : ClosedSmoothRiemannianMetric n M) :
    MeasureTheory.Integrable (fun x : M ↦ g.scalarAt x) (volumeMeasure g)
```

Scalar integral functionals:

```lean
noncomputable def totalScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  ∫ x, g.scalarAt x ∂(volumeMeasure g)

noncomputable def meanScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  totalScalar g / (volumeMeasure g Set.univ).toReal
```

Einstein constant-scalar and integral lemmas:

```lean
theorem scalarAt_eq_nat_mul_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x) (x : M) :
    g.scalarAt x = n * lam

theorem totalScalar_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x) :
    totalScalar g = (n * lam) * (volumeMeasure g Set.univ).toReal

theorem meanScalar_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x)
    (hvol : (volumeMeasure g Set.univ).toReal ≠ 0) :
    meanScalar g = n * lam

theorem meanScalar_of_forall_isEinsteinAt_of_volume_ne_zero
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hEin : ∀ x : M, g.IsEinsteinAt lam x)
    (hvol : volumeMeasure g Set.univ ≠ 0) :
    meanScalar g = n * lam
```

The volume-positivity input is isolated in the last lemma as the hypothesis
`volumeMeasure g Set.univ ≠ 0`.  The next geometric lemma should prove this
for nonempty closed Riemannian manifolds, likely from local positivity of the
Hausdorff measure in a chart plus nonempty compactness.

## Normalized-flow roadmap

The normalized Ricci-flow tensor equation is now stateable using the existing
pointwise Ricci tensor, metric tensor, and `meanScalar`:

```lean
fun x u w =>
  -2 * g.ricciAt x u w
    + (2 / (n : ℝ)) * meanScalar g * g.inner x u w
```

Suggested next interface:

```lean
def normalizedRicciFlowRHSAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TangentSpace (closedSmoothModelWithCorners n) x) : ℝ :=
  -2 * g.ricciAt x u w
    + (2 / (n : ℝ)) * meanScalar g * g.inner x u w
```

Then the normalized-flow statement can require a time-dependent metric `gt`
whose time derivative at `t` equals `normalizedRicciFlowRHSAt (gt t)` in every
tangent slot.  The scalar integral layer supplies the global average term.

## Verification

Command:

```text
lake build Poincare.Global.ScalarIntegral
```

Result:

```text
✔ [2942/2942] Built Poincare.Global.ScalarIntegral (2.7s)
Build completed successfully (2942 jobs).
```

The build emitted pre-existing lint warnings while replaying dependency
modules, but no errors.
