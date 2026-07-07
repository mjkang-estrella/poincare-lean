# M5-rigid-31 blocked: normalized-direction cutoff radius is not exported

Added `Poincare/Global/CartanDomainShrink.lean` with one verified non-vacuous statement:

```lean
theorem Poincare.CartanDomainShrink.exists_shrunk_expAt_source_cutoff_one_ball
```

It constructs a positive radius `ρ` whose ball is contained in the exp-chart
open-partial-homeomorphism source and is simultaneously small enough for the
cutoff-one PL-flow velocity radius and the interval condition `‖v‖ ∈ Icc 0 τ`;
the theorem also applies the exported PL-flow law at time `‖v‖` for the small
unnormalized velocity `v`.

Blocked statement: the requested Cartan block conversion needs the cutoff-one
PL-flow hypotheses for the normalized nonzero direction `‖v‖⁻¹ • v`, but the
current public APIs only give a small-velocity ball `‖v₀‖ < δ`, and shrinking
`‖v‖ < ρ` does not imply `‖‖v‖⁻¹ • v‖ < δ` (indeed this norm is `1` when
`v ≠ 0`), so the source/target block instantiations and the bridge-applied
local-isometry theorem would be vacuous wrappers without a new exported
unit-direction or unit-speed cutoff package.

Verification:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanDomainShrink.lean
git diff --check -- Poincare/Global/CartanDomainShrink.lean
lake build Poincare.Global.CartanDomainShrink
```

Actual result: forbidden-token scan had no matches, whitespace check succeeded,
and `lake build Poincare.Global.CartanDomainShrink` completed successfully with
pre-existing upstream warnings.  Final build line:

```text
Build completed successfully (3152 jobs).
```
