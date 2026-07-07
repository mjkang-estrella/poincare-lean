# M5-rigid-32 blocked: homogeneity conversion verified, endpoint blocks still missing

## Files

- Added `Poincare/Global/CartanHomogeneity.lean`.
- Added this report.
- Did not edit existing Lean modules or `Poincare.lean`.

## Verified progress

`CartanHomogeneity.lean` proves the small-velocity homogeneity conversion
without using the normalized unit direction as a PL-flow velocity.

Main theorem:

```lean
Poincare.CartanHomogeneity.exists_shrunk_cutoff_one_homogeneity_conversion
```

It shrinks to a positive radius `rho` contained in the source of
`GeodesicTransport.expAtChartOpenPartialHomeomorph`.  For every `v` with
`||v|| < rho`, the theorem defines

```lean
u := workingVelocity delta v = (delta / 2) • (||v||^-1 • v)
T := workingTime delta v = ||v|| / (delta / 2)
```

and proves:

- `||u|| < delta`;
- `T in Icc 0 tau`;
- `T • u = v`;
- the cutoff-one PL hypotheses hold for the working velocity `u` on
  `Icc (-tau) tau`, including target membership, closed-ball control,
  `cutoff = 1`, and the PL homogeneity law;
- `GeodesicTransport.expAt g x0 v =
  (extChartAt I x0).symm (alpha (extChartAt I x0 x0, u) T).1`;
- if `v != 0`, the radial endpoint derivative is expressed at `(u, T)`:

```lean
HasDerivAt
  (fun s : Real =>
    extChartAt I x0 (GeodesicTransport.expAt g x0 ((T + s) • u)))
  (alpha (extChartAt I x0 x0, u) T).2 0
```

The helper lemmas also prove the algebraic backbone:

```lean
norm_workingVelocity_lt
workingTime_smul_workingVelocity
workingTime_mem_Icc_of_norm_lt
workingTime_mem_Ioo_of_norm_lt
```

## Remaining isolated statement

The requested local isometry is still blocked upstream of
`CartanCoefficientBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_source_endpoint_pairings`.
The new conversion gives the correct small PL host `(u, T)`, but no exported
theorem currently turns the hosted cutoff-one PL/Jacobi interval data into the
bridge's source endpoint pairings and strict differential identifications for
the original endpoint vector `v`.

One non-vacuous next statement to prove is:

```lean
theorem homogeneity_hosted_source_endpoint_blocks
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M) :
    exists rho > 0, forall v : ClosedSmoothModel 3,
      ||v|| < rho -> v != 0 ->
        -- with u := workingVelocity delta v and T := workingTime delta v
        -- from exists_shrunk_cutoff_one_homogeneity_conversion,
        -- prove the three source endpoint pairing blocks at expAtChart v:
        -- radial-radial, radial-transverse, transverse-transverse,
        -- using transverseScale v = sin ||v|| / ||v||,
        -- and prove the source expAtChart strict derivative data needed by
        -- the Cartan chart differential identification.
```

This is not a wrapper around the bridge: it is exactly the missing conversion
from the proven interval ingredients at `(u, T)` to the endpoint block fields
consumed by the bridge.

## Verification

Commands run:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanHomogeneity.lean
git diff --check -- Poincare/Global/CartanHomogeneity.lean
lake env lean Poincare/Global/CartanHomogeneity.lean
lake build Poincare.Global.CartanHomogeneity
```

Actual result:

- forbidden-token scan found no matches;
- whitespace check succeeded;
- `lake env lean Poincare/Global/CartanHomogeneity.lean` succeeded;
- `lake build Poincare.Global.CartanHomogeneity` succeeded with pre-existing
  upstream warnings replayed.

Final build lines:

```text
Built Poincare.Global.CartanHomogeneity (3.2s)
Build completed successfully (3145 jobs).
```
