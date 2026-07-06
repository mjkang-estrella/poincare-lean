import Poincare.Global.RiemannianContext
import Poincare.Global.Statement
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The ambient pullback metric on the statement-layer three-sphere

This file records the concrete pointwise tensor underlying the round metric on
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1`: pull back the ambient
Euclidean inner product along the differential of the inclusion.
-/

noncomputable section

open Bornology Bundle
open scoped Manifold ContDiff Topology

namespace Poincare

/-- The statement-layer unit three-sphere in `ℝ⁴`. -/
abbrev RoundSphere3 : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)

/-- The ambient Euclidean space containing the statement-layer three-sphere. -/
abbrev RoundSphereAmbient4 : Type :=
  EuclideanSpace ℝ (Fin 4)

/-- The model fiber for the statement-layer three-sphere. -/
abbrev RoundSphereModel3 : Type :=
  EuclideanSpace ℝ (Fin 3)

private instance roundSphereAmbient4_finrank_fact :
    Fact (Module.finrank ℝ RoundSphereAmbient4 = 3 + 1) :=
  ⟨by simp [RoundSphereAmbient4]⟩

/-- The differential of the inclusion `S³ ⊂ ℝ⁴`. -/
noncomputable def roundSphereMetric3_inclusionDeriv (x : RoundSphere3) :
    TangentSpace (𝓡 3) x →L[ℝ] RoundSphereAmbient4 :=
  mfderiv (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4)
    ((↑) : RoundSphere3 → RoundSphereAmbient4) x

/-- Pointwise pullback of the ambient inner product along the inclusion derivative. -/
noncomputable def roundSphereMetric3_inner (x : RoundSphere3) :
    TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ :=
  let A : TangentSpace (𝓡 3) x →L[ℝ] RoundSphereAmbient4 :=
    roundSphereMetric3_inclusionDeriv x
  ((ContinuousLinearMap.precomp (𝕜₁ := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (G := ℝ) A).comp (innerSL ℝ (E := RoundSphereAmbient4))).comp A

theorem roundSphereMetric3_inner_apply (x : RoundSphere3)
    (v w : TangentSpace (𝓡 3) x) :
    roundSphereMetric3_inner x v w =
      inner ℝ (roundSphereMetric3_inclusionDeriv x v)
        (roundSphereMetric3_inclusionDeriv x w) := by
  rw [roundSphereMetric3_inner]
  simp [roundSphereMetric3_inclusionDeriv, ContinuousLinearMap.precomp]

theorem roundSphereMetric3_inner_mfderiv_eq (x : RoundSphere3)
    (v w : TangentSpace (𝓡 3) x) :
    roundSphereMetric3_inner x v w =
      inner ℝ
        (show RoundSphereAmbient4 from
          mfderiv (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4)
            ((↑) : RoundSphere3 → RoundSphereAmbient4) x v)
        (show RoundSphereAmbient4 from
          mfderiv (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4)
            ((↑) : RoundSphere3 → RoundSphereAmbient4) x w) := by
  simpa [roundSphereMetric3_inclusionDeriv] using roundSphereMetric3_inner_apply x v w

theorem roundSphereMetric3_inner_symm (x : RoundSphere3)
    (v w : TangentSpace (𝓡 3) x) :
    roundSphereMetric3_inner x v w = roundSphereMetric3_inner x w v := by
  rw [roundSphereMetric3_inner_apply, roundSphereMetric3_inner_apply]
  exact real_inner_comm _ _

theorem roundSphereMetric3_inner_pos (x : RoundSphere3)
    {v : TangentSpace (𝓡 3) x} (hv : v ≠ 0) :
    0 < roundSphereMetric3_inner x v v := by
  rw [roundSphereMetric3_inner_apply]
  refine real_inner_self_pos.2 ?_
  intro hzero
  have hA0 :
      roundSphereMetric3_inclusionDeriv x v =
        roundSphereMetric3_inclusionDeriv x 0 := by
    simpa using hzero
  exact hv ((mfderiv_coe_sphere_injective (n := 3) (E := RoundSphereAmbient4) x) hA0)

theorem roundSphereMetric3_inner_isVonNBounded (x : RoundSphere3) :
    IsVonNBounded ℝ
      {v : TangentSpace (𝓡 3) x | roundSphereMetric3_inner x v v < 1} := by
  letI : NormedAddCommGroup (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 3)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 3)))
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  let A : TangentSpace (𝓡 3) x →L[ℝ] RoundSphereAmbient4 :=
    roundSphereMetric3_inclusionDeriv x
  have hAinj : Function.Injective A :=
    mfderiv_coe_sphere_injective (n := 3) (E := RoundSphereAmbient4) x
  obtain ⟨K, _hKpos, hK⟩ :=
    (A : TangentSpace (𝓡 3) x →ₗ[ℝ] RoundSphereAmbient4).injective_iff_antilipschitz.mp hAinj
  have hbounded_preimage : Bornology.IsBounded (A ⁻¹' Metric.ball (0 : RoundSphereAmbient4) 1) :=
    hK.isBounded_preimage Metric.isBounded_ball
  refine NormedSpace.isVonNBounded_of_isBounded ℝ
    (hbounded_preimage.subset ?_)
  intro v hv
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
  have hv' : inner ℝ (A v) (A v) < 1 := by
    simpa [A, roundSphereMetric3_inner_apply] using hv
  rw [← sq_lt_one_iff₀ (norm_nonneg _)]
  simpa [real_inner_self_eq_norm_sq] using hv'

/-- Model-space pullback of the ambient inner product by a linear map. -/
noncomputable def roundSphereMetric3_modelInner
    (D : RoundSphereModel3 →L[ℝ] RoundSphereAmbient4) :
    RoundSphereModel3 →L[ℝ] RoundSphereModel3 →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precomp (𝕜₁ := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (G := ℝ) D).comp (innerSL ℝ (E := RoundSphereAmbient4))).comp D

theorem roundSphereMetric3_modelInner_eq
    (D : RoundSphereModel3 →L[ℝ] RoundSphereAmbient4) :
    roundSphereMetric3_modelInner D =
      (((ContinuousLinearMap.precompR RoundSphereModel3
        (innerSL ℝ (E := RoundSphereAmbient4))).flip D).comp D) := by
  ext v w
  simp [roundSphereMetric3_modelInner, ContinuousLinearMap.precomp]
  change inner ℝ (D v) (D w) = inner ℝ (D v) (D w)
  rfl

theorem roundSphereMetric3_modelInner_contDiff :
    ContDiff ℝ ∞ roundSphereMetric3_modelInner := by
  rw [contDiff_clm_apply_iff]
  intro v
  rw [contDiff_clm_apply_iff]
  intro w
  have hv :
      ContDiff ℝ ∞
        (fun D : RoundSphereModel3 →L[ℝ] RoundSphereAmbient4 => D v) :=
    (contDiff_id :
      ContDiff ℝ ∞
        (fun D : RoundSphereModel3 →L[ℝ] RoundSphereAmbient4 => D)).clm_apply
      contDiff_const
  have hw :
      ContDiff ℝ ∞
        (fun D : RoundSphereModel3 →L[ℝ] RoundSphereAmbient4 => D w) :=
    (contDiff_id :
      ContDiff ℝ ∞
        (fun D : RoundSphereModel3 →L[ℝ] RoundSphereAmbient4 => D)).clm_apply
      contDiff_const
  have hinner :
      ContDiff ℝ ∞
        (fun D : RoundSphereModel3 →L[ℝ] RoundSphereAmbient4 =>
          inner ℝ (D v) (D w)) := by
    simpa using (contDiff_inner (𝕜 := ℝ) (E := RoundSphereAmbient4) (n := ∞)).comp
      (hv.prodMk hw)
  simpa [roundSphereMetric3_modelInner, ContinuousLinearMap.precomp, innerSL_apply_apply]
    using hinner

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
          x (roundSphereMetric3_inner x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let Dcoord : RoundSphere3 → RoundSphereModel3 →L[ℝ] RoundSphereAmbient4 :=
    inTangentCoordinates (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4) id
      ((↑) : RoundSphere3 → RoundSphereAmbient4)
      roundSphereMetric3_inclusionDeriv x₀
  have hD :
      ContMDiffAt (𝓡 3) 𝓘(ℝ, RoundSphereModel3 →L[ℝ] RoundSphereAmbient4)
        ∞ Dcoord x₀ := by
    have hcoe :
        ContMDiffAt (𝓡 3) 𝓘(ℝ, RoundSphereAmbient4) ∞
          ((↑) : RoundSphere3 → RoundSphereAmbient4) x₀ :=
      (contMDiff_coe_sphere (m := ∞) (n := 3)
        (E := RoundSphereAmbient4)) x₀
    simpa [Dcoord, roundSphereMetric3_inclusionDeriv] using
      (hcoe.mfderiv_const (I := 𝓡 3) (I' := 𝓘(ℝ, RoundSphereAmbient4))
        (m := ∞) (n := ∞) (by simp))
  have hmodel :
      ContMDiffAt (𝓡 3)
        𝓘(ℝ, RoundSphereModel3 →L[ℝ] RoundSphereModel3 →L[ℝ] ℝ)
        ∞ (fun x : RoundSphere3 => roundSphereMetric3_modelInner (Dcoord x)) x₀ :=
    by
      simpa [Function.comp_def] using
        roundSphereMetric3_modelInner_contDiff.comp_contMDiffAt hD
  exact hmodel.congr_of_eventuallyEq (by
    filter_upwards [chart_source_mem_nhds (RoundSphereModel3) x₀] with x hx
    have hx_triv :
        x ∈ (trivializationAt RoundSphereModel3
          (fun x : RoundSphere3 => TangentSpace (𝓡 3) x) x₀).baseSet := by
      simpa using hx
    ext v w
    rw [inCoordinates_apply_eq₂ hx_triv hx_triv (Set.mem_univ x)]
    simp [Dcoord, roundSphereMetric3_modelInner, roundSphereMetric3_inner_apply,
      roundSphereMetric3_inclusionDeriv, inTangentCoordinates,
      ContinuousLinearMap.inCoordinates, ContinuousLinearMap.precomp]
    rfl)

noncomputable def roundSphereMetric3 : ClosedSmoothRiemannianMetric 3 RoundSphere3 where
  inner := roundSphereMetric3_inner
  symm := roundSphereMetric3_inner_symm
  pos := fun x _ hv => roundSphereMetric3_inner_pos x hv
  isVonNBounded := roundSphereMetric3_inner_isVonNBounded
  contMDiff := roundSphereMetric3_inner_contMDiff

@[simp]
theorem roundSphereMetric3_inner_eq :
    roundSphereMetric3.inner = roundSphereMetric3_inner :=
  rfl

end Poincare
