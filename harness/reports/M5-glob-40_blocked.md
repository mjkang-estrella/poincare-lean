# M5-glob-40 blocked: endpoint field bridge reduced to the C² producer

## Status

Blocked on the fully unconditional endpoint bridge from the augmented
second-variation data at the ball points.

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/EndpointBridge.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one theorem:

```lean
theorem Poincare.EndpointBridge
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_contDiffAt_two
```

It removes the artificial open-neighborhood endpoint-field hypothesis from
`FTransitionDone`.  Given

```lean
ContDiffAt ℝ 2 F (eM v)
```

the proof takes the canonical endpoint field

```lean
fun q : E3 => fderiv ℝ F q
```

on `Set.univ`, uses `ContDiffAt.fderiv_right` to prove

```lean
HasFDerivAt (fun q : E3 => fderiv ℝ F q)
  (fderiv ℝ (fun q : E3 => fderiv ℝ F q) (eM v)) (eM v)
```

and feeds these data into `FTransitionDone`.  The resulting transition law has
the correction term

```lean
((fderiv ℝ (fun q : E3 => fderiv ℝ F q) (eM v)) u) w
```

so the endpoint CLM is now the canonical derivative of the canonical derivative
field.

## Blocking boundary

The theorem is still not curvature-only.  The remaining hypothesis is exactly:

```lean
ContDiffAt ℝ 2 F (eM v)
```

for

```lean
let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
let F := CartanDifferential.cartanChartMap g x₀ p₀ L
```

`SecondDischarge.lean` exports a scalar-parameter augmented endpoint derivative,
and `SecondFrechet.lean` exports a generic CLM packaging theorem for a
second-variation solution family.  The repository still does not export the
neighborhood-level theorem identifying those augmented endpoint derivatives as
the derivative of the canonical field `q ↦ fderiv ℝ F q` on a neighborhood of
the punctured endpoint, nor does it export the resulting
`ContDiffAt ℝ 2 F (eM v)` from the hosted ball data.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/EndpointBridge.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/EndpointBridge.lean
git diff --check -- Poincare/Global/EndpointBridge.lean
lake build Poincare.Global.EndpointBridge
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
35:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_contDiffAt_two

git diff --check -- Poincare/Global/EndpointBridge.lean
exit status 0

lake build Poincare.Global.EndpointBridge
✔ [3230/3230] Built Poincare.Global.EndpointBridge (3.1s)
Build completed successfully (3230 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
