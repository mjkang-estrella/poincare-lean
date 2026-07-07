# M5-rigid-70 done: decomposed hosted endpoint assembly

## Status

Done.  Added `Poincare/Global/DecomposedAssembly.lean`; no existing Lean files
or `Poincare.lean` were edited.

The new module proves the radial/transverse hosted endpoint assembly:

```lean
Poincare.DecomposedAssembly.hosted_rescaled_endpoint_pairing_eq_of_radial_transverse_blocks
Poincare.DecomposedAssembly.source_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
Poincare.DecomposedAssembly.target_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
Poincare.DecomposedAssembly.hosted_endpoint_pairing_feed_of_common_speed_decomposed_blocks
Poincare.DecomposedAssembly.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_decomposed_blocks
```

The core theorem does not assume the old all-direction endpoint formula.  It
splits each input into `CartanPullback.radialPart + transversePart`, uses
endpoint additivity to expand the hosted `Ψ` endpoints, uses bilinearity of the
endpoint metric, kills the mixed hosted block by the radial/transverse block
hypothesis, and kills the mixed anchor blocks by the Gram algebra in
`CartanPullback`.  The source and target specializations then feed the existing
common-speed `SpeedGeneric` Cartan local-isometry consumer.

## Verification

Forbidden-token scan:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/DecomposedAssembly.lean
```

returned no matches.

Whitespace check:

```text
git diff --check -- Poincare/Global/DecomposedAssembly.lean
```

passed with no output.

Required build:

```text
lake build Poincare.Global.DecomposedAssembly
```

completed successfully:

```text
✔ [3180/3180] Built Poincare.Global.DecomposedAssembly (12s)
Build completed successfully (3180 jobs).
```

The build replayed pre-existing warnings from imported modules; there were no
Lean errors.
