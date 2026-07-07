# M5-glob-39 blocked: F-transition assembly reduced to endpoint derivative bridge

## Status

Blocked on the fully unconditional, curvature-only F-transition law.

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/FTransitionDone.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one theorem:

```lean
theorem Poincare.FTransitionDone
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_endpoint_hasFDerivAt_on_open
```

It uses a single `DifferentialField` witness to avoid mismatched existential
choices, then assembles the chain:

- selected punctured-ball `DF` and strict Cartan derivative;
- open-neighborhood congruence for `q ↦ fderiv ℝ F q`;
- residual export plus second-derivative symmetry;
- concrete residual-to-`HasFDerivAt (fun q => DF (eM.symm q))` upgrade;
- neighborhood pullback germ for the selected `DF` field;
- differentiated pullback identity;
- signed Christoffel transport algebra.

The conclusion is the signed target/source Christoffel transition law at
`eM v`, with correction term `(CLM u) w`, for the selected Cartan `DF v`.

## Blocking boundary

The theorem is not curvature-only.  The exact remaining shape is:

```lean
∀ (endpoint : E3 → E3 →L[ℝ] E3)
  (CLM : E3 →L[ℝ] E3 →L[ℝ] E3) (U : Set E3),
  IsOpen U →
  eM v ∈ U →
  Set.EqOn (fun q : E3 => fderiv ℝ F q) endpoint U →
  HasFDerivAt endpoint CLM (eM v) →
  ContDiffAt ℝ 2 F (eM v) →
  ...
```

The repository still does not export the non-hypothetical theorem producing
that endpoint derivative field, its open agreement with the canonical
`fderiv` field, and the `C²` Cartan-map regularity at the punctured endpoint
from curvature-only data.  The previously landed augmented-flow theorem
`SecondDischarge.lean` remains data-parametric; there is still no API
identifying its second-variation endpoint CLM with the canonical derivative
field `q ↦ fderiv ℝ F q` on an open punctured-ball neighborhood.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/FTransitionDone.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/FTransitionDone.lean
git diff --check -- Poincare/Global/FTransitionDone.lean
lake build Poincare.Global.FTransitionDone
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
43:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_endpoint_hasFDerivAt_on_open

git diff --check -- Poincare/Global/FTransitionDone.lean
exit status 0

lake build Poincare.Global.FTransitionDone
✔ [3229/3229] Built Poincare.Global.FTransitionDone (4.2s)
Build completed successfully (3229 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module
built successfully and introduced no reported warning.
