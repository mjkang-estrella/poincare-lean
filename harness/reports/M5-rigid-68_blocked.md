# M5-rigid-68 blocked: hosted speed data instantiated, endpoint orthogonality still missing

## Status

Blocked.  Added `Poincare/Global/TheLocalIsometry.lean` and did not edit
existing Lean modules, including `Poincare.lean`.

The new module proves the non-vacuous hosted facts needed after
`Poincare.Global.SpeedGeneric`:

```lean
Poincare.TheLocalIsometry.workingTime_pos_of_ne_zero
Poincare.TheLocalIsometry.workingTime_ne_zero_of_ne_zero
Poincare.TheLocalIsometry.workingVelocity_ne_zero_of_ne_zero
Poincare.TheLocalIsometry.inv_workingTime_smul_eq_workingVelocity
Poincare.TheLocalIsometry.hostedSourceSpeed_pos_of_ne_zero
Poincare.TheLocalIsometry.hostedSourceSpeed_ne_zero_of_ne_zero
Poincare.TheLocalIsometry.hostedTargetSpeed_pos_of_ne_zero
Poincare.TheLocalIsometry.hostedTargetSpeed_ne_zero_of_ne_zero
Poincare.TheLocalIsometry.source_speed_hypothesis_of_hosted_workingVelocity_on_shrunk_Icc
Poincare.TheLocalIsometry.target_speed_hypothesis_of_hosted_workingVelocity_on_shrunk_Icc
```

These instantiate the actual hosted `CartanHomogeneity.workingVelocity δ v`
curves into the source and aligned-target speed hypotheses consumed by the
speed-generic Jacobi package, using `SpeedPackage`'s speed-value theorems.

## Remaining blocker

The requested `cartanMap_isLocalIsometry`-shaped theorem was not added.  After
the speed field is discharged, the next source-side endpoint package field
that is not available from the actual hosted/cascade data is the transverse
orthogonality hypothesis in
`SourcePackage.source_hosted_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package`
as generated in `SpeedGeneric.lean`:

```lean
(horth : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
  CovariantDerivative.chartMetric g.inner x₀
    (γ s).1 (Ψ w s).1 (γ s).2 = 0)
```

The analogous target-side field is:

```lean
(horth : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
    (γ s).1 (Ψ w s).1 (γ s).2 = 0)
```

`CartanCascade.exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl`
exports all-direction hosted linearized families with
`Ψ w 0 = (0, T⁻¹ • w)`, endpoint additivity/homogeneity, and strict
derivatives.  It does not export that every all-direction Jacobi position field
is orthogonal to the hosted base velocity.  That condition is only appropriate
for transverse input directions; for radial components it is a real geometric
obligation, not a speed bookkeeping issue.

Thus adding the final local-isometry wrapper here would leave this hypothesis
assumed rather than instantiated, violating the task's no-vacuous-wrapper rule.

## Verification

Forbidden-token scan on `Poincare/Global/TheLocalIsometry.lean`: no matches for
`sorry`, `admit`, `axiom`, or `native_decide`.

Whitespace check:

```text
git diff --check -- Poincare/Global/TheLocalIsometry.lean
```

passed with no output.

Required build:

```text
lake build Poincare.Global.TheLocalIsometry
```

completed successfully:

```text
✔ [3180/3180] Built Poincare.Global.TheLocalIsometry (2.9s)
Build completed successfully (3180 jobs).
```
