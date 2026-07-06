import Poincare.Global.RoundSphereChart
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Round sphere metric coefficients in stereographic charts

This file connects the ambient stereographic conformal-factor computation from
`RoundSphereChart` to the bundled round metric `roundSphereMetric3`.
-/

noncomputable section

open Bornology Bundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare

/-- The orthogonal-complement model isometry used by Mathlib's sphere chart at `x₀`.

The chart `chartAt RoundSphereModel3 x₀` is `stereographic' 3 (-x₀)`, so its
inverse first maps coordinates through this inverse isometry and then applies
`stereoInvFunAux (-x₀)`.
-/
noncomputable def roundSphereChartModelEquiv (x₀ : RoundSphere3) :
    (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ ≃ₗᵢ[ℝ] RoundSphereModel3 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 3
    (ne_zero_of_mem_unit_sphere (-x₀ : RoundSphere3))).repr

/-- Mathlib's inverse sphere chart, viewed in the ambient `ℝ⁴`, is `stereoInvFunAux`
after the chart's orthogonal-complement model identification. -/
theorem coe_chartAt_symm_eq_stereoInvFunAux (x₀ : RoundSphere3)
    (z : RoundSphereModel3) :
    (((chartAt RoundSphereModel3 x₀).symm z : RoundSphere3) : RoundSphereAmbient4) =
      stereoInvFunAux (((-x₀ : RoundSphere3) : RoundSphereAmbient4))
        ((roundSphereChartModelEquiv x₀).symm z : RoundSphereAmbient4) := by
  change (((stereographic' 3 (-x₀ : RoundSphere3)).symm z : RoundSphere3) :
      RoundSphereAmbient4) =
      stereoInvFunAux (((-x₀ : RoundSphere3) : RoundSphereAmbient4))
        ((roundSphereChartModelEquiv x₀).symm z : RoundSphereAmbient4)
  rw [stereographic'_symm_apply]
  simp [roundSphereChartModelEquiv, stereoInvFunAux_apply, smul_add, smul_smul]

/-- Differentiating the stereographic inverse after Mathlib's chart model isometry. -/
theorem fderiv_stereoInvFunAux_chartModel_apply (x₀ : RoundSphere3)
    (z u : RoundSphereModel3) :
    fderiv ℝ (((stereoInvFunAux (((-x₀ : RoundSphere3) : RoundSphereAmbient4)) ∘
      ((↑) : (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ →
        RoundSphereAmbient4)) ∘
      (roundSphereChartModelEquiv x₀).symm)) z u =
    (fderiv ℝ (stereoInvFunAux (((-x₀ : RoundSphere3) : RoundSphereAmbient4)) ∘
      ((↑) : (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ →
        RoundSphereAmbient4))
      ((roundSphereChartModelEquiv x₀).symm z)) ((roundSphereChartModelEquiv x₀).symm u) := by
  let pole : RoundSphereAmbient4 := (((-x₀ : RoundSphere3) : RoundSphereAmbient4))
  let U := roundSphereChartModelEquiv x₀
  have hbaseDiff :
      DifferentiableAt ℝ
        (stereoInvFunAux pole ∘ ((↑) : (ℝ ∙ pole)ᗮ → RoundSphereAmbient4)) (U.symm z) := by
    have hsub : HasFDerivAt ((↑) : (ℝ ∙ pole)ᗮ → RoundSphereAmbient4)
        (ℝ ∙ pole)ᗮ.subtypeL (U.symm z) := by
      simpa using (ℝ ∙ pole)ᗮ.subtypeL.hasFDerivAt
    exact ((hasFDerivAt_stereoInvFunAuxFDeriv pole
      ((U.symm z : (ℝ ∙ pole)ᗮ) : RoundSphereAmbient4)).comp (U.symm z) hsub).differentiableAt
  have hUdiff : DifferentiableAt ℝ (U.symm) z :=
    U.symm.toContinuousLinearEquiv.differentiableAt
  have hUf : fderiv ℝ (U.symm) z =
      (U.symm : RoundSphereModel3 →L[ℝ] (ℝ ∙ pole)ᗮ) := by
    exact U.symm.toContinuousLinearEquiv.fderiv
  change fderiv ℝ
      ((stereoInvFunAux pole ∘ ((↑) : (ℝ ∙ pole)ᗮ → RoundSphereAmbient4)) ∘ U.symm) z u =
    (fderiv ℝ (stereoInvFunAux pole ∘ ((↑) : (ℝ ∙ pole)ᗮ → RoundSphereAmbient4))
      (U.symm z)) (U.symm u)
  rw [fderiv_comp z hbaseDiff hUdiff, hUf]
  rfl

/-- The ambient pullback by Mathlib's inverse chart is conformal with the stereographic factor. -/
theorem inner_fderiv_coe_chartAt_symm (x₀ : RoundSphere3)
    (z u w : RoundSphereModel3) :
    inner ℝ
      (fderiv ℝ (fun y : RoundSphereModel3 =>
        (((chartAt RoundSphereModel3 x₀).symm y : RoundSphere3) :
          RoundSphereAmbient4)) z u)
      (fderiv ℝ (fun y : RoundSphereModel3 =>
        (((chartAt RoundSphereModel3 x₀).symm y : RoundSphere3) :
          RoundSphereAmbient4)) z w) =
      stereoInvFunAuxConformalFactor
        (((roundSphereChartModelEquiv x₀).symm z :
          (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ) :
          RoundSphereAmbient4) *
        inner ℝ u w := by
  let pole : RoundSphereAmbient4 := (((-x₀ : RoundSphere3) : RoundSphereAmbient4))
  let U := roundSphereChartModelEquiv x₀
  have hfun :
      (fun y : RoundSphereModel3 =>
        (((chartAt RoundSphereModel3 x₀).symm y : RoundSphere3) :
          RoundSphereAmbient4)) =
        ((stereoInvFunAux pole ∘ ((↑) : (ℝ ∙ pole)ᗮ → RoundSphereAmbient4)) ∘
          U.symm) := by
    funext y
    simp [pole, U, coe_chartAt_symm_eq_stereoInvFunAux]
  rw [hfun]
  rw [fderiv_stereoInvFunAux_chartModel_apply, fderiv_stereoInvFunAux_chartModel_apply]
  change inner ℝ
      ((fderiv ℝ (stereoInvFunAux pole ∘ ((↑) : (ℝ ∙ pole)ᗮ → RoundSphereAmbient4))
        (U.symm z)) (U.symm u))
      ((fderiv ℝ (stereoInvFunAux pole ∘ ((↑) : (ℝ ∙ pole)ᗮ → RoundSphereAmbient4))
        (U.symm z)) (U.symm w)) =
      stereoInvFunAuxConformalFactor ((U.symm z : (ℝ ∙ pole)ᗮ) : RoundSphereAmbient4) *
        inner ℝ u w
  have hv : ‖pole‖ = 1 := by
    simp [pole]
  have hbase :=
    inner_fderiv_stereoInvFunAux_comp_subtype (v := pole) hv (U.symm z) (U.symm u) (U.symm w)
  rw [hbase]
  have hinner : inner ℝ (U.symm u) (U.symm w) = inner ℝ u w :=
    U.symm.inner_map_map u w
  rw [hinner]

/-- Chain-rule bridge from the manifold inclusion derivative after inverse chart coordinates
to the ordinary Fréchet derivative of the ambient chart parametrization. -/
theorem mfderiv_coe_comp_chartAt_symm_apply (x₀ : RoundSphere3)
    (z u : RoundSphereModel3) :
    mfderiv (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4)
      ((↑) : RoundSphere3 → RoundSphereAmbient4)
      ((chartAt RoundSphereModel3 x₀).symm z)
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) z u) =
    fderiv ℝ (fun y : RoundSphereModel3 =>
      (((chartAt RoundSphereModel3 x₀).symm y : RoundSphere3) :
        RoundSphereAmbient4)) z u := by
  have hz : z ∈ (chartAt RoundSphereModel3 x₀).target := by
    change z ∈ (stereographic' 3 (-x₀ : RoundSphere3)).target
    simp
  have hsymm : MDifferentiableAt 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
      ((chartAt RoundSphereModel3 x₀).symm) z := by
    exact mdifferentiableAt_atlas_symm (I := 𝓡 3)
      (chart_mem_atlas RoundSphereModel3 x₀) hz
  have hcoe : MDifferentiableAt (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4)
      ((↑) : RoundSphere3 → RoundSphereAmbient4)
      ((chartAt RoundSphereModel3 x₀).symm z) := by
    exact (contMDiff_coe_sphere (m := 1) (n := 3)
      (E := RoundSphereAmbient4)).mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp_apply
      (I := 𝓘(ℝ, RoundSphereModel3)) (I' := 𝓡 3)
      (I'' := 𝓘(ℝ, RoundSphereAmbient4))
      (f := ((chartAt RoundSphereModel3 x₀).symm))
      (g := ((↑) : RoundSphere3 → RoundSphereAmbient4)) z hcoe hsymm u
  rw [← hchain]
  rw [mfderiv_eq_fderiv]
  rfl

/-- In Mathlib's stereographic chart at `x₀`, the round three-sphere metric is the
Euclidean inner product multiplied by `16 / (‖z‖² + 4)²`, with `z` first transported
through the chart's orthogonal-complement model isometry. -/
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
        inner ℝ u w := by
  rw [roundSphereMetric3_inner_eq]
  rw [roundSphereMetric3_inner_mfderiv_eq]
  rw [mfderiv_coe_comp_chartAt_symm_apply, mfderiv_coe_comp_chartAt_symm_apply]
  exact inner_fderiv_coe_chartAt_symm x₀ z u w

/-- Source-point version of `roundSphereMetric3_inner_chartAt_symm_eq`, with
`z = chartAt RoundSphereModel3 x₀ p`. -/
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
        inner ℝ u w := by
  have h :=
    roundSphereMetric3_inner_chartAt_symm_eq x₀ ((chartAt RoundSphereModel3 x₀) p) u w
  have hp_inv : (chartAt RoundSphereModel3 x₀).symm ((chartAt RoundSphereModel3 x₀) p) = p :=
    (chartAt RoundSphereModel3 x₀).left_inv hp
  rw [hp_inv] at h
  simpa using h

end Poincare
