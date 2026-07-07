# M5-rigid-66 blocked: G-normalized speed is proved, hosting replay still lacks a PL radius export

## Status

Added `Poincare/Global/NormalizedHosting.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module defines the source anchor-metric normalization

```lean
sourceNormalizedTime g x₀ v :=
  Real.sqrt (CartanMap.sourceAnchorChartMetric g x₀ v v)

sourceNormalizedVelocity g x₀ v :=
  (sourceNormalizedTime g x₀ v)⁻¹ • v
```

and proves the nonzero endpoint algebra needed for frequency-one hosting:

```lean
Poincare.NormalizedHosting.sourceNormalizedTime_pos
Poincare.NormalizedHosting.sourceNormalizedTime_ne_zero
Poincare.NormalizedHosting.sourceNormalizedTime_smul_sourceNormalizedVelocity
Poincare.NormalizedHosting.sourceNormalizedTime_pos_smul
Poincare.NormalizedHosting.sourceNormalizedVelocity_pos_smul
Poincare.NormalizedHosting.sourceAnchorChartMetric_sourceNormalizedVelocity_self
Poincare.NormalizedHosting.sourceNormalizedTime_smul_alignedTargetNormalizedVelocity
Poincare.NormalizedHosting.targetAnchorChartMetric_alignedTargetNormalizedVelocity_self
Poincare.NormalizedHosting.hosted_source_curve_unit_speed_on_shrunk_Icc
Poincare.NormalizedHosting.hosted_aligned_target_curve_unit_speed_on_shrunk_Icc
```

The central proved facts are:

```lean
CartanMap.sourceAnchorChartMetric g x₀
  (sourceNormalizedVelocity g x₀ v)
  (sourceNormalizedVelocity g x₀ v) = 1
```

for `v ≠ 0`, and, for any tangent alignment `L`,

```lean
CartanMap.targetAnchorChartMetric p₀
  (alignedTargetNormalizedVelocity L v)
  (alignedTargetNormalizedVelocity L v) = 1
```

with the same source-normalized time.  The hosted source and aligned target
unit-speed theorems feed these identities through the speed-value package from
`SpeedPackage.lean`, so the old package-level `hunit` shape is discharged
whenever the existing PL hypotheses are available at the normalized working
velocity.

## Remaining blocker

The full `CartanHomogeneity` replay cannot currently be completed from the
exported PL machinery.  The available public theorem is still a small Euclidean
velocity-ball statement:

```lean
GeodesicTransport.expAt_uniform_pl_flow_cutoff_one_eq_on_Icc :
  ∃ τ > 0, ∃ δ > 0, ∃ a : NNReal, ∃ α,
    (∀ v₀ : E, ‖v₀‖ < δ → ...) ∧
    ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc 0 τ, ...
```

To replay hosting with

```lean
u := sourceNormalizedVelocity g x₀ v
T := sourceNormalizedTime g x₀ v
```

one must supply the missing hypothesis

```lean
‖sourceNormalizedVelocity g x₀ v‖ < δ
```

for the `δ` exported by that theorem.  Shrinking the endpoint does not provide
this.  The new theorem

```lean
sourceNormalizedVelocity_pos_smul :
  0 < c →
  sourceNormalizedVelocity g x₀ (c • v) =
    sourceNormalizedVelocity g x₀ v
```

formally records the obstruction: G-normalized velocity is ray-invariant.
Thus a smaller normal ball for `v` changes `T` but not `u`, so it cannot force
the Euclidean smallness condition `‖u‖ < δ`.

The next required export is a PL/cutoff-one flow package on a velocity set large
enough to contain the source anchor-metric unit sphere, for example a theorem
parameterized by an arbitrary Euclidean velocity radius `R` with a sufficiently
small time interval, or a compact-velocity-set variant.  With such an export,
the unit-speed lemmas in `NormalizedHosting.lean` should provide the exact
`hunit` input for the existing source and target packages.

## Verification

Placeholder scan on the new Lean file: no forbidden placeholders or declarations
were found.

Whitespace check:

```bash
git diff --check -- Poincare/Global/NormalizedHosting.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.NormalizedHosting
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module emitted no local errors.

Final build lines:

```text
✔ [3160/3160] Built Poincare.Global.NormalizedHosting (2.6s)
Build completed successfully (3160 jobs).
```
