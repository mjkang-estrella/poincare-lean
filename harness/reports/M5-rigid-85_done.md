# M5-rigid-85 done: solution additivity replaces centered linearized PL

## Status

Added `Poincare/Global/SolutionsFeed.lean`.  No existing Lean files were edited.

The new feed path removes the centered

```lean
hplLinear : ∀ w w', IsPicardLindelof ... ((0 : E3), T⁻¹ • (w + w')) ...
```

dependency from the bounded transverse polarization step.  Instead it consumes
the hosted solution-family endpoint additivity

```lean
∀ w w' : E3, (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1
```

which is exported by `LinearizedAdditivity.lean`.

## New lemmas

- `SolutionsFeed.actual_jacobi_pairing_eq_scalar_of_quadratic_and_endpoint_add`
  polarizes directly from the three quadratic identities plus endpoint
  additivity, without uniqueness or centered PL hypotheses.
- `SolutionsFeed.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_solutions_on_closedBall`
  is the source bounded closed-ball feed variant with `hplLinear`,
  `hmem_add`, and `hmem_sum` removed.
- `SolutionsFeed.target_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_solutions_on_closedBall`
  mirrors the source variant for the round-sphere target.
- `SolutionsFeed.source_transverseTransverse_of_solutions_feed` and
  `SolutionsFeed.target_transverseTransverse_of_solutions_feed` extend the
  closed-ball result using the existing homogeneity lemmas and produce the
  transverse-transverse block shape consumed by `BundleDischarge`.

## Verification

- `lake build Poincare.Global.SolutionsFeed Poincare.Global.BoundedPackage`
  - Result: success.
  - Final lines:

```text
✔ [3193/3193] Built Poincare.Global.SolutionsFeed (12s)
Build completed successfully (3193 jobs).
```

## Hygiene

- Forbidden-token scan on `Poincare/Global/SolutionsFeed.lean` found no
  `sorry`, `admit`, `axiom`, or `native_decide`.
