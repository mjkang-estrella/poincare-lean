import Poincare.Global.ConformalCurvature
import Poincare.Global.GeodesicTransport
import Poincare.Global.RoundSphereChartMetric

/-!
# Round sphere curvature transport intermediates

This file records the chart-side bridges needed to transport the concrete
stereographic sphere curvature calculation to the bundled round metric on
`RoundSphere3`.  The final manifold-level curvature transport theorem is still
blocked on a missing bridge from chart `modelLeviCivita` curvature back to
`roundSphereMetric3.leviCivita` curvature on canonical manifold extensions.
-/

noncomputable section

open CovariantDerivative Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology

namespace CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/--
Christoffel one-forms are germ-local in the metric coefficient field and
point-local in the bilinear form used to lower indices.
-/
theorem christoffelOneForm_congr_of_eventuallyEq
    {G G' : F → F →L[ℝ] F →L[ℝ] ℝ}
    {b b' : F → LinearMap.BilinForm ℝ F}
    {hb : ∀ x, (b x).Nondegenerate} {hb' : ∀ x, (b' x).Nondegenerate}
    {z s v : F}
    (hG : G =ᶠ[𝓝 z] G') (hbz : b z = b' z) :
    (christoffelOneForm G b hb z) s v =
      (christoffelOneForm G' b' hb' z) s v := by
  rw [christoffelOneForm_apply, christoffelOneForm_apply]
  set A := christoffelAt G z (b z) (hb z) v s
  set B := christoffelAt G' z (b' z) (hb' z) v s
  apply sub_eq_zero.mp
  apply (hb' z).1
  intro w
  change (b' z (A - B)) w = 0
  rw [show b' z (A - B) = b' z A - b' z B by exact map_sub (b' z) A B]
  simp only [LinearMap.sub_apply]
  have hf : fderiv ℝ G z = fderiv ℝ G' z := hG.fderiv_eq
  have hleft : b' z A w = b z A w := by
    rw [hbz]
  rw [hleft]
  subst A
  subst B
  rw [b_christoffelAt, b_christoffelAt]
  rw [hf]
  ring

end CovariantDerivative

namespace Poincare

/-- The round-sphere chart model isometry preserves the stereographic conformal factor. -/
theorem stereoInvFunAuxConformalFactor_roundSphereChartModelEquiv_symm
    (x₀ : RoundSphere3) (z : RoundSphereModel3) :
    stereoInvFunAuxConformalFactor
        (((roundSphereChartModelEquiv x₀).symm z :
          (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ) :
          RoundSphereAmbient4) =
      stereoInvFunAuxConformalFactor z := by
  unfold stereoInvFunAuxConformalFactor
  rw [show ‖(((roundSphereChartModelEquiv x₀).symm z :
        (ℝ ∙ (((-x₀ : RoundSphere3) : RoundSphereAmbient4)))ᗮ) :
        RoundSphereAmbient4)‖ = ‖z‖ by
    simpa using (roundSphereChartModelEquiv x₀).symm.norm_map z]

/--
In the stereographic chart anchored at `x₀`, the transported coefficient family
of `roundSphereMetric3` is exactly the stereographic conformal metric.
-/
theorem roundSphereMetric3_chartMetric_eq (x₀ : RoundSphere3)
    (z u w : RoundSphereModel3) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner x₀ z u w =
      stereoInvFunAuxConformalFactor z * inner ℝ u w := by
  rw [CovariantDerivative.chartMetric_apply]
  rw [(closedSmoothModelWithCorners 3).range_eq_univ, mfderivWithin_univ]
  change roundSphereMetric3.inner ((chartAt RoundSphereModel3 x₀).symm z)
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) z u)
      (mfderiv 𝓘(ℝ, RoundSphereModel3) (𝓡 3)
        ((chartAt RoundSphereModel3 x₀).symm) z w) =
      stereoInvFunAuxConformalFactor z * inner ℝ u w
  rw [roundSphereMetric3_inner_chartAt_symm_eq]
  exact congrArg (fun c => c * inner ℝ u w)
    (stereoInvFunAuxConformalFactor_roundSphereChartModelEquiv_symm x₀ z)

/--
On the cutoff-one zone, the blended chart metric used by geodesic transport is
the stereographic conformal flat metric.
-/
theorem roundSphereMetric3_blendedChartMetric_eq_conformal_of_cutoff_one
    (x₀ : RoundSphere3) {z : RoundSphereModel3}
    (hz : GeodesicTransport.cutoff (n := 3) x₀ z = 1) :
    CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3))
        roundSphereMetric3.inner x₀ z =
      conformalFlatMetric
        (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z := by
  ext u w
  rw [CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one _ _ _ _ hz]
  rw [roundSphereMetric3_chartMetric_eq]
  simp [conformalFlatMetric]

/-- Bilinear-form version of `roundSphereMetric3_blendedChartMetric_eq_conformal_of_cutoff_one`. -/
theorem roundSphereMetric3_chartBilin_eq_conformal_of_cutoff_one
    (x₀ : RoundSphere3) {z : RoundSphereModel3}
    (hz : GeodesicTransport.cutoff (n := 3) x₀ z = 1) :
    CovariantDerivative.chartBilin
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3))
        roundSphereMetric3.inner x₀ z =
      conformalFlatBilin
        (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z := by
  ext u w
  change CovariantDerivative.blendedChartMetric
      (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3))
      roundSphereMetric3.inner x₀ z u w =
    stereoInvFunAuxConformalFactor z * inner ℝ u w
  rw [roundSphereMetric3_blendedChartMetric_eq_conformal_of_cutoff_one x₀ hz]
  simp [conformalFlatMetric]

/--
Near the chart anchor, the blended metric coefficients are germ-equal to the
stereographic conformal flat coefficients.
-/
theorem roundSphereMetric3_blendedChartMetric_eventuallyEq_conformal
    (x₀ : RoundSphere3) :
    (fun z : RoundSphereModel3 =>
      CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3))
        roundSphereMetric3.inner x₀ z)
      =ᶠ[𝓝 (extChartAt (𝓡 3) x₀ x₀)]
    (fun z : RoundSphereModel3 =>
      conformalFlatMetric
        (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z) := by
  filter_upwards [GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x₀] with z hz
  exact roundSphereMetric3_blendedChartMetric_eq_conformal_of_cutoff_one x₀ hz

/-- Euclidean gradient representative of the stereographic conformal factor. -/
theorem stereoInvFunAuxConformalFactor_grad
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z w : E) :
    inner ℝ ((-64 * ((‖z‖ ^ 2 + 4) ^ 3)⁻¹) • z) w =
      fderiv ℝ (stereoInvFunAuxConformalFactor : E → ℝ) z w := by
  rw [fderiv_stereoInvFunAuxConformalFactor]
  simp [stereoInvFunAuxConformalFactorFDeriv, inner_smul_left]
  have hden : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  field_simp [hden]
  ring

/--
The conformal Christoffel one-form for the stereographic sphere factor is the
explicit `sphereChristoffel` field.
-/
theorem christoffelOneForm_stereoInvFunAuxConformalFactor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (z s v : E) :
    (CovariantDerivative.christoffelOneForm
      (conformalFlatMetric (stereoInvFunAuxConformalFactor : E → ℝ))
      (conformalFlatBilin (stereoInvFunAuxConformalFactor : E → ℝ))
      (fun y => conformalFlatBilin_nondegenerate
        (stereoInvFunAuxConformalFactor : E → ℝ) y
        (by dsimp [stereoInvFunAuxConformalFactor]; positivity)) z) s v =
      sphereChristoffel z s v := by
  let gradf : E := (-64 * ((‖z‖ ^ 2 + 4) ^ 3)⁻¹) • z
  have hgrad : ∀ w : E,
      inner ℝ gradf w =
        fderiv ℝ (stereoInvFunAuxConformalFactor : E → ℝ) z w := by
    intro w
    exact stereoInvFunAuxConformalFactor_grad z w
  have hfd :
      DifferentiableAt ℝ (stereoInvFunAuxConformalFactor : E → ℝ) z :=
    (hasFDerivAt_stereoInvFunAuxConformalFactor z).differentiableAt
  rw [christoffelOneForm_conformalFlatMetric_apply
    (stereoInvFunAuxConformalFactor : E → ℝ)
    (by intro y; dsimp [stereoInvFunAuxConformalFactor]; positivity)
    hfd hgrad]
  simp [conformalChristoffelFormula, gradf, sphereChristoffel_apply,
    sphereChristoffelCoreFormula, sphereChristoffelCoeff,
    stereoInvFunAuxConformalFactor, smul_add, smul_smul, sub_eq_add_neg]
  rw [← hgrad v, ← hgrad s]
  simp [gradf, inner_smul_left]
  have hden : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  have hden4 : 4 + ‖z‖ ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring_nf
  rw [show 128 + ‖z‖ ^ 2 * 32 = 32 * (4 + ‖z‖ ^ 2) by ring]
  have hcoef (c : ℝ) :
      c * (32 * (4 + ‖z‖ ^ 2))⁻¹ * 64 =
        c * (4 + ‖z‖ ^ 2)⁻¹ * 2 := by
    field_simp [hden4]
    ring
  have hcoef_comm (c : ℝ) :
      (32 * (4 + ‖z‖ ^ 2))⁻¹ * c * 64 =
        c * (4 + ‖z‖ ^ 2)⁻¹ * 2 := by
    field_simp [hden4]
    ring
  rw [hcoef (inner ℝ z v), hcoef_comm (inner ℝ z s),
    hcoef_comm (inner ℝ v s)]
  rw [real_inner_comm v s]
  abel_nf
  simp
  abel

/--
If the geodesic-transport cutoff is germ-equal to one at `z`, the transported
round-sphere chart Christoffel field is the explicit sphere Christoffel field.
-/
theorem roundSphereMetric3_chartChristoffelField_eq_sphereChristoffel_of_eventuallyEq_one
    (x₀ : RoundSphere3) {z : RoundSphereModel3}
    (hχ : (fun y : RoundSphereModel3 =>
        GeodesicTransport.cutoff (n := 3) x₀ y) =ᶠ[𝓝 z] fun _ => (1 : ℝ))
    (s v : RoundSphereModel3) :
    GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀ z s v =
      sphereChristoffel z s v := by
  have hG :
      (fun y : RoundSphereModel3 =>
        CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := 3) x₀)
          (GeodesicTransport.backgroundMetric (n := 3))
          roundSphereMetric3.inner x₀ y)
        =ᶠ[𝓝 z]
      (fun y : RoundSphereModel3 =>
        conformalFlatMetric
          (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) y) := by
    filter_upwards [hχ] with y hy
    exact roundSphereMetric3_blendedChartMetric_eq_conformal_of_cutoff_one x₀ hy
  have hbz :
      CovariantDerivative.chartBilin
          (GeodesicTransport.cutoff (n := 3) x₀)
          (GeodesicTransport.backgroundMetric (n := 3))
          roundSphereMetric3.inner x₀ z =
        conformalFlatBilin
          (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z :=
    roundSphereMetric3_chartBilin_eq_conformal_of_cutoff_one x₀
      (hχ.self_of_nhds)
  change
    (CovariantDerivative.christoffelOneForm
      (CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3))
        roundSphereMetric3.inner x₀)
      (CovariantDerivative.chartBilin
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3))
        roundSphereMetric3.inner x₀)
      (CovariantDerivative.chartBilin_nondegenerate
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3))
        (GeodesicTransport.backgroundMetric_pos (n := 3))
        roundSphereMetric3.inner
        (fun y u hu => roundSphereMetric3.inner_pos y (v := u) hu)
        x₀
        (GeodesicTransport.cutoff_nonneg (n := 3) x₀)
        (GeodesicTransport.cutoff_le_one (n := 3) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := 3) x₀))
      z) s v =
    sphereChristoffel z s v
  rw [CovariantDerivative.christoffelOneForm_congr_of_eventuallyEq hG hbz]
  exact christoffelOneForm_stereoInvFunAuxConformalFactor z s v

/-- Anchor specialization of the round-sphere chart Christoffel bridge. -/
theorem roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel
    (x₀ : RoundSphere3) (s v : RoundSphereModel3) :
    GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀
        (extChartAt (𝓡 3) x₀ x₀) s v =
      sphereChristoffel (extChartAt (𝓡 3) x₀ x₀) s v :=
  roundSphereMetric3_chartChristoffelField_eq_sphereChristoffel_of_eventuallyEq_one
    x₀ (GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x₀) s v

end Poincare
