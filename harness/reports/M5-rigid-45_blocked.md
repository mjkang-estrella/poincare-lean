# M5-rigid-45 blocked: cascade reaches source/target CLM strict derivatives

## Status

Blocked for the full requested unconditional local-isometry theorem.  I added
the new module `Poincare/Global/CartanCascade.lean` with one isolated,
verified theorem and did not edit existing Lean modules, including
`Poincare.lean`.

## Verified payload

The module exports exactly one theorem:

```lean
Poincare.CartanCascade.exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl
```

For a source metric `g`, source anchor `x₀`, target anchor `p₀`, and tangent
alignment `align`, it chooses one positive source radius `ρ` such that every
`‖v‖ < ρ` satisfies both:

```lean
v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source
align v ∈ (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀).source
```

On the source side and on the aligned round-sphere target side, the theorem
then consumes the corresponding hosted linearized Picard-Lindelöf data,
applies

```lean
LinearizedAdditivity.exists_hosted_rescaled_linearized_solution_family_endpoint_linear
```

to construct the all-direction family with endpoint additivity and homogeneity,
packages its endpoint as `linearizedEndpointCLM`, and feeds that into

```lean
GeodesicTransport.exists_shrunk_expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_linearized_family
```

The result is a source strict derivative at `v` and a target strict derivative
at `align v`, each with the constructed `linearizedEndpointCLM` value.

This is not a vacuous wrapper around the final hosted-scale bridge: it uses
M5-rigid-44 endpoint linearity to discharge the CLM hypotheses required by the
M5-rigid-40 strict-derivative theorem on both sides.  The common radius also
uses continuity of `align.toContinuousLinearEquiv` to keep `align v` inside the
target shrunk ball.

## Remaining blocker

The final theorem requested by the task still cannot honestly be stated as an
unconditional call to

```lean
CartanScaleGeneric.cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings
```

from the currently exported API.  That bridge still requires:

1. continuous-linear-equivalence endpoint differentials `A B : E ≃L[ℝ] E`,
   while the verified cascade now produces strict derivatives whose values are
   `linearizedEndpointCLM : E →L[ℝ] E`;
2. the `hDu` and `hDu'` equations for
   `CartanLocalIsometry.cartanChartDifferential L A B`;
3. the three hosted source endpoint metric blocks in the exact
   `CartanScaleGeneric` source-block shape.

Assuming these remaining objects in `CartanCascade.lean` would amount to
restating the hosted-scale bridge with its hard inputs still assumed, so I
stopped at the verified source/target strict-derivative cascade boundary.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanCascade.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/CartanCascade.lean
```

Actual result:

```text
43:theorem exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/CartanCascade.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanCascade
```

Actual result: succeeded, with pre-existing upstream warnings replayed.

Final build lines:

```text
Built Poincare.Global.CartanCascade (3.1s)
Build completed successfully (3166 jobs).
```
