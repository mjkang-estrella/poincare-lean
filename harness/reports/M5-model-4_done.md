# M5-model-4 done: round metric coefficients in Mathlib sphere charts

## Completed

- Added `Poincare/Global/RoundSphereChartMetric.lean`.
- Proved the Mathlib chart model identification
  `roundSphereChartModelEquiv x₀`, matching
  `chartAt RoundSphereModel3 x₀ = stereographic' 3 (-x₀)`.
- Proved the reusable `mfderiv`/`fderiv` bridge
  `mfderiv_coe_comp_chartAt_symm_apply`.
- Proved the coordinate coefficient theorem for `roundSphereMetric3`, plus a
  source-point corollary using `p ∈ (chartAt RoundSphereModel3 x₀).source`.

## Final statements

```lean
noncomputable def roundSphereChartModelEquiv (x₀ : RoundSphere3) :
    (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ ≃ₗᵢ[ℝ] RoundSphereModel3

theorem coe_chartAt_symm_eq_stereoInvFunAux (x₀ : RoundSphere3)
    (z : RoundSphereModel3) :
    (((chartAt RoundSphereModel3 x₀).symm z : RoundSphere3) : RoundSphereAmbient4) =
      stereoInvFunAux (((-x₀ : RoundSphere3) : RoundSphereAmbient4))
        ((roundSphereChartModelEquiv x₀).symm z : RoundSphereAmbient4)

theorem mfderiv_coe_comp_chartAt_symm_apply (x₀ : RoundSphere3)
    (z u : RoundSphereModel3) :
    mfderiv (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4)
      ((↑) : RoundSphere3 → RoundSphereAmbient4)
      ((chartAt RoundSphereModel3 x₀).symm z)
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) z u) =
    fderiv ℝ (fun y : RoundSphereModel3 =>
      (((chartAt RoundSphereModel3 x₀).symm y : RoundSphere3) :
        RoundSphereAmbient4)) z u

theorem roundSphereMetric3_inner_chartAt_symm_eq (x₀ : RoundSphere3)
    (z u w : RoundSphereModel3) :
    roundSphereMetric3.inner ((chartAt RoundSphereModel3 x₀).symm z)
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) z u)
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) z w) =
      stereoInvFunAuxConformalFactor
        (((roundSphereChartModelEquiv x₀).symm z :
          (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ) :
          RoundSphereAmbient4) *
        inner ℝ u w

theorem roundSphereMetric3_inner_chartAt_source_eq (x₀ p : RoundSphere3)
    (hp : p ∈ (chartAt RoundSphereModel3 x₀).source) (u w : RoundSphereModel3) :
    roundSphereMetric3.inner p
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) ((chartAt RoundSphereModel3 x₀) p) u)
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) ((chartAt RoundSphereModel3 x₀) p) w) =
      stereoInvFunAuxConformalFactor
        (((roundSphereChartModelEquiv x₀).symm ((chartAt RoundSphereModel3 x₀) p) :
          (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ) :
          RoundSphereAmbient4) *
        inner ℝ u w
```

## Curvature roadmap

The chart coefficient is now the conformal metric
`g_ij(z) = stereoInvFunAuxConformalFactor ((roundSphereChartModelEquiv x₀).symm z) * δ_ij`
in Mathlib's chart coordinates. The next computation can:

1. Rewrite `stereoInvFunAuxConformalFactor` as `16 / (‖U.symm z‖ ^ 2 + 4) ^ 2`, then use
   `U.symm.inner_map_map` to replace `‖U.symm z‖` by `‖z‖`.
2. Feed the scalar conformal factor into local Christoffel coefficient formulas.
3. Compute the curvature operator coefficients in the same chart and package the constant as
   the derived sectional-curvature normalization for `roundSphereMetric3`.

## Verification

Command run:

```bash
lake build Poincare.Global.RoundSphereChartMetric
```

Actual result: success (`Build completed successfully (2846 jobs).`).

The new Lean file contains no `sorry`, no new `axiom`, and no `native_decide`.
