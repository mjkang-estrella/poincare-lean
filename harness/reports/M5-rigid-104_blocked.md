# M5-rigid-104 blocked: corrected radial block prevents full sin² pullbacks

## Outcome

Added `Poincare/Global/SinSqInstantiate.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The requested curvature-only theorem was not stated.  The remaining
instantiation is not merely a missing adapter: the corrected selector-level
radial block is incompatible with the full scalar pullback shape required by
`ScaledUpgrade.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pullbacks`,
except at the special scalar value `Real.sin θ ^ 2 = 1`.

## Verified obstruction

The new module proves the generic obstruction:

```lean
Poincare.SinSqInstantiate.time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
```

It states that if a hosted family satisfies the actual time-radial radial block

```lean
G ((Ψ (CartanPullback.radialPart S v u) T).1)
  ((Ψ (CartanPullback.radialPart S v u') T).1) =
  CorrectedRadial.timeRadialScale T *
    S (T⁻¹ • CartanPullback.radialPart S v u)
      (T⁻¹ • CartanPullback.radialPart S v u')
```

and also a full sine-square pullback

```lean
∀ a a' : E3,
  G (Ψ a T).1 (Ψ a' T).1 = Real.sin θ ^ 2 * S a a'
```

then `Real.sin θ ^ 2 = 1`.

The file also specializes this to the source and target anchor metrics:

```lean
Poincare.SinSqInstantiate.source_time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
Poincare.SinSqInstantiate.target_time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
```

## Blocker

The corrected block chain available from `SpeedReconcile`/`CorrectedRadial`
has a plain time-radial factor and a speed-pinned transverse factor.  The
full-scalar `sin²` pullback needed by `ScaledUpgrade` would require the radial
line to carry the same `sin²` scalar.  Lean now proves that this forces
`sin² = 1`, which is not exported by the selector and is stronger than the
available `θ ∈ Set.Ioo 0 Real.pi`.

Therefore feeding `ScaledUpgrade` at the selector datum would require assuming
the missing full sine-square pullbacks, which would be a vacuous wrapper around
the actual obstruction.

## Verification

- Contract-token scan on `Poincare/Global/SinSqInstantiate.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/SinSqInstantiate.lean`
  - Result: success.
- `lake build Poincare.Global.SinSqInstantiate`
  - Result: success.  The build replayed pre-existing imported-module
    warnings; no failure was emitted from `Poincare/Global/SinSqInstantiate.lean`.
  - Final lines:

```text
✔ [3204/3204] Built Poincare.Global.SinSqInstantiate (13s)
Build completed successfully (3204 jobs).
```
