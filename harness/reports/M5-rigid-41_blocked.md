# M5-rigid-41 blocked: source action equation strict partial

## Status

Blocked for the full local-isometry instantiation.  I added the new module
`Poincare/Global/CartanActionEquations.lean` with one isolated, verified
statement for the source-side CLM action equation.  I did not edit existing
Lean files, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.CartanActionEquations.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic
```

It proves the radial/transverse source action equation for a fixed
`linearizedEndpointCLM`.  The radial action is supplied as the ray-law input,
and the transverse action is proved from

```lean
jacobi_position_eq_sin_smul_on_Icc
```

after identifying the endpoint value with a harmonic Jacobi state at the
rescaled time `speed * T`.  The resulting transverse coefficient is the hosted
scale

```lean
CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T
```

so the conclusion is:

```lean
linearizedEndpointCLM (Psi := Psi) T hadd hsmul u =
  CartanLocalIsometry.sourceScaledNormalVector g x0 rho
    (CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T) v u
```

This is not a wrapper around the hosted-scale bridge: it uses the CLM
linearity, radial/transverse decomposition, the supplied radial action, and the
Jacobi coordinate value to produce the source action equation.

## Remaining blocker

The full target requested by M5-rigid-41 still needs upstream exports that are
not available in the current API:

1. a concrete hosted `Psi` family for every endpoint `v`, on the same interval
   required by the strict derivative theorem, with endpoint additivity/smul;
2. the radial action theorem from the hosted ray-law derivative in the exact
   CLM form consumed by the new action-equation theorem;
3. the target-side analogue and the algebra converting source/target endpoint
   CLM actions into the `hDu`/`hDu'` equations for
   `CartanLocalIsometry.cartanChartDifferential`;
4. the three hosted source endpoint metric blocks needed by
   `CartanScaleGeneric.cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings`.

Calling the hosted bridge today would still require re-assuming those missing
families, so I stopped at the verified non-vacuous action-equation partial.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanActionEquations.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/CartanActionEquations.lean
```

Actual result:

```text
40:theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/CartanActionEquations.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanActionEquations
```

Actual result: succeeded, with pre-existing upstream warnings replayed.

Final build lines:

```text
Built Poincare.Global.CartanActionEquations (2.9s)
Build completed successfully (3160 jobs).
```
