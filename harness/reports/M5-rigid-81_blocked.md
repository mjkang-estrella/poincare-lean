# M5-rigid-81 blocked: PL norm feed lands, hosted hplNorm still not exported

## Status

Added `Poincare/Global/PLNormFeed.lean` as the requested new module.  No
existing Lean files were edited, including `Poincare.lean`.

The new module verifies the downstream feed: if the source and target
speed-generic Picard-Lindelöf norm packages are supplied at the common hosted
datum, then the source and target transverse-transverse endpoint blocks land in
exactly the shape consumed by `BundleDischarge`.

It does **not** construct the requested hosted `hplNorm` packages themselves.
That remains the blocking field.

## What landed

New transverse orthogonality helpers:

```lean
Poincare.PLNormFeed.sourceAnchorChartMetric_transversePart_eq_zero
Poincare.PLNormFeed.targetAnchorChartMetric_transversePart_eq_zero
```

New source/target PL-norm feed lemmas:

```lean
Poincare.PLNormFeed.source_transverseTransverse_of_plNorm_feed
Poincare.PLNormFeed.target_transverseTransverse_of_plNorm_feed
```

These are not vacuous wrappers: each applies the existing
`SourcePackage`/`TargetPackage` speed-generic interval theorem to the actual
transverse parts and proves the anchor transversality hypotheses needed by
those theorems.

## Remaining boundary

The first field still not supplied by the hosted exports is the same source
field isolated in `M5-rigid-80`:

```lean
(hplNorm : ∀ w : E3,
  IsPicardLindelof
    (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
    (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
    ((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
```

The target analogue is the same statement with `roundSphereMetric3` and `p₀`.

`GeodesicLengthFinal`/`CartanHomogeneity` export the hosted base geodesic PL
flow and cutoff data.  They do not export this scalar norm-system PL package.
The reusable continuous-linear-ODE helper in `GeodesicLinearized` constructs PL
constants after fixing an initial center, while the required `hplNorm` field
has one shared `(radius, rNorm, LNorm, KNorm)` outside `∀ w`.  I found no
current theorem that supplies that uniform field at the hosted datum.

## Verification

- `lake build Poincare.Global.PLNormFeed`
  - Result: success.
  - Final lines:

```text
✔ [3190/3190] Built Poincare.Global.PLNormFeed (11s)
Build completed successfully (3190 jobs).
```

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/PLNormFeed.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/PLNormFeed.lean`
  - Result: passed.
