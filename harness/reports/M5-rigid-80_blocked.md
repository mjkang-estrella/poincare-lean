# M5-rigid-80 blocked: bundle discharge boundary

## Status

Blocked for the curvature-only `cartanMap_isLocalIsometry` target.  Proof-bearing
bundle progress was added in `Poincare/Global/BundleDischarge.lean`; no existing
Lean module was edited, including `Poincare.lean`.

## What landed

- Added source and target rescaled anchor-orthogonality lemmas for
  `T⁻¹ • transversePart ...`.
- Specialized the one-sided `Icc 0 T` payload exports to the hosted endpoint data
  used by the bundle consumer.
- Added
  `Poincare.BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`,
  which feeds the discharged source/target transverse orthogonality into
  `CombinedFeed`, then through `SpeedReconcile` and the corrected `T ^ 2`
  radial consumer in `CorrectedRadial`.

This is not a vacuous wrapper: the source and target transverse-orthogonality
inputs are proved from the one-sided payload hypotheses and rewritten to the
endpoint/velocity data expected by the downstream consumer.

## Remaining boundary

The one-sided `hflow` interval mismatch is resolved.  The remaining obstruction
is that the current exports still do not co-quantify the `SpeedGeneric`
interval norm package, and therefore the transverse-transverse endpoint blocks,
with the same common hosted datum `(T, PsiS, PsiT, speed)`.

The first field that cannot yet be supplied from the common exported cascade is
verbatim:

```lean
(hplNorm : ∀ w : E3,
  IsPicardLindelof
    (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
    (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
    ((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
```

This is the source-side `SpeedGeneric` norm package used to produce the
transverse-transverse block.  The target side has the analogous field with
`roundSphereMetric3` and `p₀`.

## Verification

- `lake build Poincare.Global.BundleDischarge`
  - Result: success.
  - Final line: `Build completed successfully (3189 jobs).`
  - The final `BundleDischarge` module built without a local warning; replayed
    imported modules still emitted their pre-existing warnings.
- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/BundleDischarge.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/BundleDischarge.lean harness/reports/M5-rigid-80_blocked.md`
  - Result: passed.
