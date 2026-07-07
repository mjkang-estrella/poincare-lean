# M5-rigid-112 done

## Outcome

Added `Poincare/Global/RigidityComplete.lean` and assembled the final
curvature-only Cartan local-isometry theorem:

```lean
Poincare.RigidityComplete.cartanMap_isLocalIsometry
```

For every closed smooth Riemannian metric `g` with
`HasConstantSectionalCurvature3 g 1`, anchors `x₀ p₀`, and tangent alignment
`L`, the theorem produces a punctured shrunk normal ball and a common positive
time such that every nonzero vector in the ball has endpoint equivalences
`A B` whose Cartan chart differential is strict and whose target chart metric
pullback equals the source chart metric for all tangent pairs.

The assembly adds the final scalar selector floor

```lean
T ≤ 1 / (2 * (4 * max (1 : ℝ) S + 1))
```

where `S` is the closed-ball source anchor speed-square bound, and also threads
the angle floor needed for positivity of the speed-pinned transverse scale.

## New supporting exports

- `speedNormSystemAop`
- `exists_source_anchor_speed_sq_bound_on_closedBall`
- `source_transverseTransverse_of_selector_aop_bound`
- `target_transverseTransverse_of_selector_aop_bound`
- `exists_equiv_and_cartanMap_isLocalIsometry_pullback_of_angle_time_blocks`
- `cartanMap_isLocalIsometry_of_selector_aop_bound`
- `cartanMap_isLocalIsometry`

## Verification

Commands run:

```bash
lake env lean Poincare/Global/RigidityComplete.lean
lake build Poincare.Global.RigidityComplete
rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/RigidityComplete.lean
git diff --check
```

Actual result:

- `lake env lean Poincare/Global/RigidityComplete.lean`: passed.
- `lake build Poincare.Global.RigidityComplete`: passed; final line was
  `Build completed successfully (3214 jobs).`
- forbidden-token scan: no matches.
- `git diff --check`: passed.
