# M5-rigid-46 done: diagonal action upgrades CLM to equivalence

## Status

Done.  I added the new module `Poincare/Global/CartanEquivUpgrade.lean` and
did not edit existing Lean modules, including `Poincare.lean`.

## Verified payload

The module exports exactly one theorem:

```lean
Poincare.CartanEquivUpgrade.exists_continuousLinearEquiv_of_sourceScaledNormalVector_action
```

For a continuous linear endpoint map `D : E →L[ℝ] E`, if `D` acts on every
vector as

```lean
CartanLocalIsometry.sourceScaledNormalVector g x₀ ρ σ v
```

and both diagonal factors satisfy `ρ ≠ 0` and `σ ≠ 0`, the theorem constructs

```lean
∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D
```

The proof is the requested invertibility step.  It uses
`CartanPullback.radialPart_add_transversePart` for spanning, the source anchor
metric positivity lemma to handle the nonzero radial vector case, the
transverse orthogonality lemma to force the radial kernel component to vanish,
and `LinearEquiv.ofInjectiveEndo` to upgrade injectivity to an equivalence in
finite dimension.  The `v = 0` case is handled separately, where the action is
just nonzero transverse scaling.

This is a strict partial toward the hosted bridge: the remaining bridge inputs
are the action equations instantiating `hD` for the source and target endpoint
CLMs, the nonzero hosted transverse-scale shrink, and the source/target metric
blocks.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanEquivUpgrade.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/CartanEquivUpgrade.lean
```

Actual result:

```text
39:theorem exists_continuousLinearEquiv_of_sourceScaledNormalVector_action
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/CartanEquivUpgrade.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanEquivUpgrade
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings,
but the new module itself emitted no local warnings after cleanup.

Final build lines:

```text
✔ [3161/3161] Built Poincare.Global.CartanEquivUpgrade (2.4s)
Build completed successfully (3161 jobs).
```
