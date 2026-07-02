# M3-predicates-40 blocked report

## Summary

The curvature-entry derivative bridge itself is now proved in
`Poincare/Global/ScalarVariation.lean`.

New theorem surface:

```lean
closedCurvatureEntryDerivativeBridgeAt_of_curvatureFieldMDifferentiableAt
```

It is the direct curvature analogue of
`deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt`: metric
compatibility differentiates the scalar pairing, and
`closedCurvatureCovDerivAt` is unfolded to rearrange the covariant curvature
derivative into the three curvature-slot corrections plus the output-slot
Levi-Civita correction.

I stopped short of declaring the task fully done because the task also asked
for the fixed canonical metric's curvature-field differentiability witness to
be derived from smoothness.  That witness is still not available from the
current public closed Levi-Civita regularity API.

## Added bridge vocabulary

```lean
closedCurvatureFieldAt
ClosedCurvatureFieldMDifferentiableAt
ClosedCurvatureEntryDerivativeBridgeAt
closedCurvatureEntryDerivativeBridgeAt_of_curvatureFieldMDifferentiableAt
```

The differentiability predicate is non-vacuous:

```lean
def ClosedCurvatureFieldMDifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  ∀ u w z : TM x,
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
      (T% (closedCurvatureFieldAt g u w z)) x
```

The bridge proves:

```lean
extDerivFun
  (fun y : M =>
    g.inner y
      (CovariantDerivative.curvatureOp g.leviCivita
        (extend E a) (extend E u) (extend E w) y)
      (extend E q y)) x v
=
  g.inner x (closedCurvatureCovDerivAt g x v a u w) q
  + g.inner x (R (nabla_v a) u w) q
  + g.inner x (R a (nabla_v u) w) q
  + g.inner x (R a u (nabla_v w)) q
  + g.inner x (R a u w) (nabla_v q)
```

with the displayed `R` abbreviating the corresponding
`CovariantDerivative.curvatureOp g.leviCivita` terms in the Lean statement.

## Remaining exact goal state

The next theorem needed to make this bridge canonical is:

```lean
theorem closedCurvatureFieldMDifferentiableAt_canonical
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    ClosedCurvatureFieldMDifferentiableAt g x
```

Equivalently, for every `u w z : TM x`, prove differentiability at `x` of:

```lean
fun y : M =>
  CovariantDerivative.curvatureOp g.leviCivita
    (extend E u) (extend E w) (extend E z) y
```

Unfolding `curvatureOp` shows this requires differentiability of iterated
covariant-derivative fields such as:

```lean
fun y : M =>
  g.leviCivita
    (fun p : M => g.leviCivita (extend E z) p (extend E w p))
    y (extend E u y)
```

The current closed global instance is only:

```lean
ClosedSmoothRiemannianMetric.leviCivita_contMDiff :
  CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1
```

and the local helper currently exposed by `LocalConnectionRegularity.lean` is:

```lean
CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt
```

which gives first differentiability of a single covariant derivative from a
locally `C2` section.  It does not supply the `C2` regularity of
`y => nabla_{extend w} extend z` needed to differentiate the outer covariant
derivative.

There is an order-polymorphic chart theorem:

```lean
CovariantDerivative.chartLeviCivita_contMDiff
```

but the closed chart-transport/global wrapper currently specializes the result
to `1`:

```lean
CovariantDerivative.chartTransportedLeviCivitaHom_contMDiffAt
LeviCivitaExistence.closedLeviCivitaConnection_contMDiff
```

So the remaining non-vacuous path is to generalize the closed Levi-Civita
regularity wrapper and the localized covariant-derivative regularity lemma to
the order needed for curvature-field differentiability.

## Ricci chain status

I did not chain into:

```lean
∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y
```

That still requires the canonical curvature-field differentiability witness
above plus the anchored Gram/Ricci trace step described in
`M3-predicates-39_blocked.md`.

## Verification

Targeted local check:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with existing warnings only.

Required build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success, with existing warnings only, ending with:

```text
Build completed successfully (2806 jobs).
```
