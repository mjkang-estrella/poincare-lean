# M3-predicates-39 blocked report

## Summary

The requested neighborhood witness

```lean
∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y
```

was not discharged.

I did not change the frozen predicate, add a `sorry`, add an `axiom`, or add an
assumption-only wrapper.  The missing piece is exactly the derivative-level
closed curvature-trace bridge described by the task: an anchored Gram/curvature
trace formula plus a curvature-entry exterior-derivative theorem.

## What was checked first

Read and obeyed `harness/worker_contract.md`.

Read `harness/reports/M3-predicates-38_done.md`; it correctly identifies the
remaining bridge input as:

```lean
∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y
```

The current worktree was clean before investigation.

## Current exact predicate

`ClosedRicciDerivativeExpansionAt` is:

```lean
def ClosedRicciDerivativeExpansionAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ v u w : TM x,
    extDerivFun
        (fun y : M ↦ g.ricciAt y (extend E u y) (extend E w y)) x v =
      closedCovRicciDerivAt g x v u w
        + g.ricciAt x (g.leviCivita (extend E u) x v) w
        + g.ricciAt x u (g.leviCivita (extend E w) x v)
```

After refreshing the module artifact with:

```bash
lake build Poincare.Global.ScalarVariation
```

the direct proof probe:

```lean
example
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    ClosedRicciDerivativeExpansionAt g x := by
  intro v u w
  unfold closedCovRicciDerivAt closedCurvatureCovDerivAt
  simp
```

reduces to the real missing equality:

```lean
extDerivFun (fun y => g.ricciAt y (extend E u y) (extend E w y)) x v =
  ∑ i, (Module.finBasis ℝ (TM x)).coord i
    ((g.leviCivita
        (fun y =>
          g.leviCivita.curvatureOp
            (extend E ((Module.finBasis ℝ (TM x)) i))
            (extend E u) (extend E w) y) x) v
      - g.leviCivita.curvatureOp
          (extend E ((g.leviCivita
            (extend E ((Module.finBasis ℝ (TM x)) i)) x) v))
          (extend E u) (extend E w) x
      - g.leviCivita.curvatureOp
          (extend E ((Module.finBasis ℝ (TM x)) i))
          (extend E ((g.leviCivita (extend E u) x) v))
          (extend E w) x
      - g.leviCivita.curvatureOp
          (extend E ((Module.finBasis ℝ (TM x)) i))
          (extend E u)
          (extend E ((g.leviCivita (extend E w) x) v)) x)
```

up to the two Ricci slot-correction traces.  Rewriting those two Ricci terms
with `ricciAt_eq_curvature_contraction` cancels the slot-correction trace
terms algebraically.  The remaining non-algebraic obligation is the exterior
derivative of the moving Ricci trace.

## Anchored trace obstruction

The closest existing pointwise theorem is:

```lean
ricciAt_eq_curvature_contraction
```

It rewrites Ricci at a point as a curvature trace in that point's tangent
basis.  A direct anchored rewrite probe fails because the theorem produces the
moving `TM y` basis and doubly extended slots:

```lean
g.ricciAt y (extend E u y) (extend E w y) =
  ∑ i, ((Module.finBasis ℝ (TM y)).repr
    (g.leviCivita.curvatureOp
      (extend E ((Module.finBasis ℝ (TM y)) i))
      (extend E (extend E u y))
      (extend E (extend E w y)) y)) i
```

but the derivative bridge needs an anchored trace over `TM x`:

```lean
∑ i, ((Module.finBasis ℝ (TM x)).repr
  (g.leviCivita.curvatureOp
    (extend E ((Module.finBasis ℝ (TM x)) i))
    (extend E u) (extend E w) y)) i
```

This is why the task's Gram route is necessary: the pointwise theorem alone
cannot transport the trace basis through the moving point.

## Exact missing theorem surfaces

The next non-vacuous theorem needed for this atom is a closed curvature-entry
derivative bridge, analogous to `DeltaGammaEntryDerivativeBridgeAt` but for
curvature values:

```lean
extDerivFun
  (fun y : M =>
    g.inner y
      (g.leviCivita.curvatureOp
        (extend E a y) (extend E u y) (extend E w y) y)
      (extend E q y)) x v
=
  g.inner x (closedCurvatureCovDerivAt g x v a u w) q
  + curvature slot/output Levi-Civita correction terms
```

Together with an anchored Gram trace formula for Ricci curvature entries,
this should imply:

```lean
theorem closedRicciDerivativeExpansionAt_of_contMDiff_inner
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    ∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y
```

The existing `g.contMDiff_inner` and `g.leviCivita_contMDiff` instances do not
currently expose this curvature-entry derivative theorem.  Adding a hypothesis
that directly states it would simply rename the missing atom, so I stopped
under the worker contract.

## Exact current goal state

The remaining target is still:

```lean
∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y
```

Once this is proved, the already-committed M3-predicates-38 bridges consume it:

```lean
eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt
eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt
```

## Verification

Initial artifact refresh:

```bash
lake build Poincare.Global.ScalarVariation
```

Result: success, with existing warnings only, ending with:

```text
Build completed successfully (2805 jobs).
```

Final standing checks:

```bash
rg -n '\b(sorry|admit|axiom|native_decide)\b' \
  Poincare/Global/ScalarVariation.lean Poincare/Global/ScalarEvolution.lean
git diff --check
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Results:

- Forbidden-placeholder scan on the two Lean modules: no matches.
- Whitespace check: success.
- Requested two-module build: success, with existing warnings only, ending with
  `Build completed successfully (2806 jobs).`
