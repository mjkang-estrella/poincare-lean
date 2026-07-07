# M5-rigid-44 done: endpoint linearity for the rescaled hosted family

## Status

Strict partial landed in the new module
`Poincare/Global/LinearizedAdditivity.lean`.  I did not edit existing Lean
modules, including `Poincare.lean`.

## Verified payload

The module exports exactly one theorem:

```lean
Poincare.LinearizedAdditivity.exists_hosted_rescaled_linearized_solution_family_endpoint_linear
```

Given the hosted zero-centered Picard-Lindelöf data, positive PL input radius,
and `T ∈ Icc (-ε) ε`, the theorem constructs the same concrete all-direction
rescaled family as `LinearizedRescale` and proves:

```lean
∀ w, Ψ w 0 = ((0 : E), T⁻¹ • w)
∀ w t ∈ Icc (-ε) ε, Ψ w solves the hosted linearized ODE at t
∀ w w', (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1
∀ c w,  (Ψ (c • w) T).1 = c • (Ψ w T).1
```

The endpoint additivity and scalar homogeneity proofs are non-vacuous.  They
compare common scaled-down curves inside the original zero-centered PL ball:
for additivity the common scale dominates `scale (w+w')` and
`scale w + scale w'`; for homogeneity it dominates `scale (c•w)` and
`|c| * scale w`.  The scaled curves solve the same linear ODE with the same
initial value, so `linearODE_solution_uniqueOn_Icc` gives equality on the
interval, and scaling back gives the endpoint identities.

## Remaining boundary

This closes the CLM additivity/smul hypotheses for the rescaled hosted family
under the same hosted PL input plus `T ∈ Icc (-ε) ε`.  The next local-isometry
assembly step is to instantiate this theorem at the per-`v` hosted data inside
`CartanIsometryClose.lean`, package `linearizedEndpointCLM`, and combine it
with the radial/transverse action equations.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/LinearizedAdditivity.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/LinearizedAdditivity.lean
```

Actual result:

```text
39:theorem exists_hosted_rescaled_linearized_solution_family_endpoint_linear
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/LinearizedAdditivity.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.LinearizedAdditivity
```

Actual result: succeeded, with pre-existing upstream warnings replayed.

Final build lines:

```text
Built Poincare.Global.LinearizedAdditivity (5.5s)
Build completed successfully (3165 jobs).
```
