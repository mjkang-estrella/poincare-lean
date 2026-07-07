# M5-rigid-26 done: scalar norm-system integration

## Files

- Added `Poincare/Global/JacobiIntegrated.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Verified strict partial

The new module contains one isolated non-vacuous statement:

```lean
theorem Poincare.JacobiIntegrated.closed_norm_system_eq_pinned_on_Icc
```

This proves the scalar ODE integration stage after the pointwise bridge from
`JacobiNormClose.chart_linearized_state_feeds_norm_system_at`.

Given:

- a continuous-linear operator whose action is exactly the closed system
  `(a,b,c) ↦ (2b, c-a, -2b)`,
- Picard-Lindelöf data for that operator on `Icc tmin tmax`,
- interval derivative hypotheses `a' = 2b`, `b' = c - a`, `c' = -2b`,
- closed-ball membership for the actual and pinned states, and
- initial data `(a(0), b(0), c(0)) = (0,0,q)`,

the theorem proves, for every `t ∈ Icc tmin tmax`:

```lean
a t = Real.sin t ^ 2 * q
b t = (Real.sin t * Real.cos t) * q
c t = Real.cos t ^ 2 * q
```

The proof builds the product state `(a,b,c)`, builds the pinned state from
`JacobiNormSystem.pinnedA/B/C`, discharges the pinned derivative side using the
already-proven derivative lemmas, and applies
`linearODE_solution_uniqueOn_Icc`.

## Remaining boundary

This file does not yet package the full geometric interval theorem from the
honest cutoff-one-shrunk flow.  The remaining downstream work is to show that
the hypotheses of `closed_norm_system_eq_pinned_on_Icc` are supplied along the
flow by `chart_linearized_state_feeds_norm_system_at`, including the interval
zone/target/cutoff-one/unit-speed/orthogonality hypotheses, then polarize and
feed the coefficient identities into the Cartan pullback/local-isometry
assembly.

## Verification

Forbidden-placeholder scan on `Poincare/Global/JacobiIntegrated.lean` found no
matches.

Top-level declaration scan found exactly one declaration:

```text
30:theorem closed_norm_system_eq_pinned_on_Icc
```

Required build:

```bash
lake build Poincare.Global.JacobiIntegrated
```

Actual result: success. Final output ended with:

```text
✔ [3150/3150] Built Poincare.Global.JacobiIntegrated (10s)
Build completed successfully (3150 jobs).
```

The build replayed existing upstream warnings; it emitted no errors from the
new module.
