# M5-glob-42 blocked: exponential chart C2 handoff isolated

## Status

Blocked on the fully non-hypothetical chart-side `C2` producer from the
augmented smooth-dependence chain.

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/ExpChartC2.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.ExpChartC2
  .cartanChartMap_contDiffAt_two_of_expChart_derivative_fields
```

For

```lean
let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0
let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
  (g := roundSphereMetric3) p0
```

the theorem proves

```lean
ContDiffAt ℝ 2 (CartanDifferential.cartanChartMap g x0 p0 L) (eM v)
```

from the concrete chart-side derivative-field package:

```lean
v ∈ eM.source
∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q
ContDiffAt ℝ 1 sourceD v
HasFDerivAt eM (sourceIso : E3 →L[ℝ] E3) v
∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q
ContDiffAt ℝ 1 targetD (L v)
```

Internally the proof performs the intended final handoff:

- `contDiffAt_succ_iff_hasFDerivAt` turns each `C1` derivative field into the
  corresponding exponential-chart `ContDiffAt ℝ 2` fact.
- `OpenPartialHomeomorph.contDiffAt_symm` turns the source chart `C2` fact and
  invertible derivative into `ContDiffAt ℝ 2 eM.symm (eM v)`.
- `ContDiffTwo.cartanChartMap_contDiffAt_two_of_expChart_contDiffAt_two`
  assembles the Cartan composition.

## Blocking boundary

This does not close the task's requested non-hypothetical chart-side analysis.
The repository still does not export the actual derivative fields

```lean
sourceD : E3 → E3 →L[ℝ] E3
targetD : E3 → E3 →L[ℝ] E3
```

from the augmented flow, with neighborhood-level derivative agreement and
`ContDiffAt ℝ 1` regularity.  The existing augmented results remain
directional/data-parametric:

- `SecondDischarge.lean` gives fixed-time scalar-parameter augmented
  derivatives from supplied geodesic/linearized/second-variation data.
- `SecondFrechet.lean` packages a second-variation endpoint family as a CLM
  under supplied linear-ODE uniqueness hypotheses.

There is still no exported theorem identifying those endpoint CLMs with the
canonical field `q ↦ fderiv ℝ (expAtChartOpenPartialHomeomorph ...) q` on a
neighborhood, nor the resulting `C1` derivative-field package needed to
instantiate the new theorem without additional hypotheses.  Consequently the
curvature-only F-transition law is still blocked at the concrete chart `C2`
producer.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/ExpChartC2.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ExpChartC2.lean
git diff --check -- Poincare/Global/ExpChartC2.lean
lake build Poincare.Global.ExpChartC2
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
39:theorem cartanChartMap_contDiffAt_two_of_expChart_derivative_fields

git diff --check -- Poincare/Global/ExpChartC2.lean
exit status 0

lake build Poincare.Global.ExpChartC2
✔ [3146/3146] Built Poincare.Global.ExpChartC2 (2.5s)
Build completed successfully (3146 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
