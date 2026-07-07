# M5-rigid-27 done: cutoff-one interval scalar assembly

## Files

- Added `Poincare/Global/CartanIsometryTheorem.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Verified strict partial

The new module contains one isolated non-vacuous statement:

```lean
theorem Poincare.CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc
```

This proves the first assembly step after `M5-rigid-26`: the pointwise bridge

```lean
JacobiNormClose.chart_linearized_state_feeds_norm_system_at
```

is quantified over a cutoff-one interval and converted into the closed scalar
system hypotheses required by

```lean
JacobiIntegrated.closed_norm_system_eq_pinned_on_Icc
```

For the actual corrected chart-linearized scalars

```lean
z τ = (γ τ).1
J τ = (Ψ τ).1
D τ = (Ψ τ).2 + Γ (γ τ).1 (γ τ).2 (Ψ τ).1
```

the theorem proves, for every `t ∈ Icc tmin tmax`,

```lean
normA g x₀ z J t = Real.sin t ^ 2 * q
normB g x₀ z J D t = (Real.sin t * Real.cos t) * q
normC g x₀ z D t = Real.cos t ^ 2 * q
```

under the explicit interval hypotheses: genuine geodesic and linearized
states, target/cutoff-one/unit-speed/transverse hypotheses, metric
differentiability along the base, Picard-Lindelöf data, closed-ball membership,
and initial data `(0,0,q)`.

## Remaining boundary

This file does not yet package the full exp-chart coefficient formula or the
Cartan local-isometry statement.  The remaining downstream step is to polarize
the transverse quadratic identity using linearity of the linearized solution,
combine it with the radial-radial and radial-transverse Gauss identities, and
then feed the resulting source/target exp-chart coefficient formulas through
the normal-coordinate Cartan pullback.

## Verification

Forbidden-placeholder scan on `Poincare/Global/CartanIsometryTheorem.lean`
found no matches.

Top-level declaration scan found exactly one declaration:

```text
40:theorem actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc
```

Required build:

```bash
lake build Poincare.Global.CartanIsometryTheorem
```

Actual result: success. Final output ended with:

```text
✔ [3151/3151] Built Poincare.Global.CartanIsometryTheorem (14s)
Build completed successfully (3151 jobs).
```

The build replayed existing upstream warnings; it emitted no errors from the
new module.
