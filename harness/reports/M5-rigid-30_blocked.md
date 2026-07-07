# M5-rigid-30 blocked: block instantiation source-shape mismatch

## Files

- Added `Poincare/Global/CartanBlocksInstantiate.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## What was checked

The downstream bridge from `M5-rigid-29` is available:

```lean
Poincare.CartanCoefficientBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_source_endpoint_pairings
```

It consumes three endpoint block hypotheses over every nonzero

```lean
v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source
```

and also still needs the strict endpoint-chart derivatives plus the
identification of the Cartan chart differential with the radial/transverse
scaled target vector.

The cited geometric ingredients are available, but their public APIs remain
one level lower:

- `CartanIsometryPackage.actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique`
  proves the transverse-transverse Jacobi pairing only after explicit interval
  PL data, three quadratic hypotheses from `CartanIsometryTheorem`, and
  linearized-flow hypotheses are supplied.
- `GeodesicTransport.expAt_uniform_pl_flow_cutoff_one_eq_on_Icc` supplies a
  cutoff-one PL flow only under radius/interval hypotheses:

```lean
‖v₀‖ < δ
t ∈ Icc (0 : ℝ) τ
```

- The radial and mixed endpoint derivative/Gauss lemmas in
  `CartanDifferential` and `GaussLemmaIntegrated` also take the same explicit
  PL/Jacobi/cutoff interval data.

## Isolated shape mismatch

There is no exported theorem converting the bridge's source-domain hypothesis

```lean
hvsrc :
  v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source
```

into the cutoff-one PL/Jacobi endpoint package needed to instantiate the three
blocks at `t = ‖v‖`:

```lean
∃ τ > 0, ∃ δ > 0, ∃ a : ℝ≥0, ∃ α,
  ‖(‖v‖)⁻¹ • v‖ < δ ∧ ‖v‖ ∈ Icc (0 : ℝ) τ ∧
  -- PL flow, target, cutoff-one, expAt ray law, linearized/Jacobi data,
  -- and the strict derivative/radial-transverse differential identification.
```

Without this source-point-to-cutoff-one-flow bridge, proving the final
unconditional theorem in `CartanBlocksInstantiate.lean` would only restate the
M5-rigid-29 bridge while still assuming the three blocks and derivative
identifications.  I did not add that vacuous wrapper.

## Verification

Forbidden-placeholder scan on `Poincare/Global/CartanBlocksInstantiate.lean`
found no matches.

Required build:

```bash
lake build Poincare.Global.CartanBlocksInstantiate
```

Actual result: success. Final output ended with:

```text
✔ [3158/3158] Built Poincare.Global.CartanBlocksInstantiate (12s)
Build completed successfully (3158 jobs).
```

The build replayed existing upstream warnings and emitted no warning from
`Poincare/Global/CartanBlocksInstantiate.lean`.
