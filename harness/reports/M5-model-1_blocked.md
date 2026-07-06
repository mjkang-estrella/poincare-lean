# M5-model-1 blocked: round S3 metric smoothness field

## Verified progress

- Added `Poincare/Global/RoundSphereMetric.lean`.
- Defined the pointwise pullback tensor
  `roundSphereMetric3_inner : TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ`
  using the inclusion derivative
  `mfderiv (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4) ((↑) : RoundSphere3 → RoundSphereAmbient4) x`.
- Proved the defining ambient-pullback equality:

  ```lean
  roundSphereMetric3_inner_mfderiv_eq
  ```

- Proved the standalone structure-field lemmas:

  ```lean
  roundSphereMetric3_inner_symm
  roundSphereMetric3_inner_pos
  roundSphereMetric3_inner_isVonNBounded
  ```

  Positivity uses Mathlib's `mfderiv_coe_sphere_injective`; boundedness uses
  finite-dimensional antilipschitzness of the injective inclusion derivative
  and boundedness of the ambient Euclidean unit ball.

- `lake build Poincare.Global.RoundSphereMetric` completed successfully for
  these standalone lemmas.

## Missing field

The only missing field for the frozen constructor is the smoothness of the
operator-valued tensor section:

```lean
theorem roundSphereMetric3_inner_contMDiff :
    ContMDiff (𝓡 3)
      ((𝓡 3).prod
        𝓘(ℝ, (EuclideanSpace ℝ (Fin 3)) →L[ℝ]
          (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ))
      ∞
      (fun x : RoundSphere3 =>
        TotalSpace.mk'
          ((EuclideanSpace ℝ (Fin 3)) →L[ℝ]
            (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ)
          x (roundSphereMetric3_inner x))
```

With that lemma, the requested definition is immediate:

```lean
noncomputable def roundSphereMetric3 : ClosedSmoothRiemannianMetric 3 RoundSphere3 where
  inner := roundSphereMetric3_inner
  symm := roundSphereMetric3_inner_symm
  pos := fun x v hv => roundSphereMetric3_inner_pos x hv
  isVonNBounded := roundSphereMetric3_inner_isVonNBounded
  contMDiff := roundSphereMetric3_inner_contMDiff
```

No placeholder `roundSphereMetric3` definition was added, per the worker
contract.

## Decomposition plan

1. Use `contMDiff_coe_sphere` plus `ContMDiffAt.mfderiv_const` to prove the
   inclusion derivative is smooth in tangent coordinates around every base
   point `x0`:

   ```lean
   CMDiffAt ∞
     (inTangentCoordinates (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))
       id ((↑) : RoundSphere3 → RoundSphereAmbient4)
       (fun x => mfderiv (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4)
         ((↑) : RoundSphere3 → RoundSphereAmbient4) x)
       x0)
     x0
   ```

2. Prove the local trivialization equation for the bilinear-form bundle:
   after applying `trivializationAt` to the section
   `x |-> roundSphereMetric3_inner x`, the fiber coordinate is exactly
   `pullbackInner (D x)`, where `D x` is the coordinate derivative from step 1.

3. Prove the model-space operation
   `D |-> ((precomp D).comp innerSL).comp D` is `ContDiff ℝ ∞` as a map
   from `EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)` to
   `(EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ`,
   using `ContinuousLinearMap.compL`, `ContinuousLinearMap.precomp`, and the
   existing `ContDiff.clm_apply`/`ContinuousLinearMap.contDiff` APIs.

4. Combine steps 1-3 through `contMDiffAt_section`, then close the global
   `ContMDiff` proof by introing the base point.
