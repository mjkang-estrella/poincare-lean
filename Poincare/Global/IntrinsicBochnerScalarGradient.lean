import Poincare.Global.ScalarGradientEvolution
import Poincare.Global.IntrinsicLaplacianCoordinateForm

noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
universe u
namespace Poincare.IntrinsicBochnerScalarGradient
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

omit [T2Space M] in
/-- The blended metric at the anchor is the intrinsic metric in that fiber. -/
theorem anchor_metric_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M)
    (v w : ClosedSmoothModel 3) :
    anchorBlendedMetricFlow (fun _ ↦ g) x 0
      (extChartAt (closedSmoothModelWithCorners 3) x x) v w = g.inner x v w := by
  have hb := (anchorBlendedMetricFlow_eventuallyEq_anchorChartMetricFlow
    (fun _ ↦ g) 0 x).self_of_nhds
  dsimp only [Function.uncurry] at hb
  rw [hb]
  have hc := CovariantDerivative.chartMetric_apply_chart
    g.inner x (mem_extChartAt_source x) v w
  rw [mfderiv_extChartAt_self] at hc
  simpa [anchorChartMetricFlow] using hc

/-- On a neighborhood of the anchor, raising the scalar differential commutes
with transport into the blended chart. -/
theorem transported_gradient_eventuallyEq
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hf : MDifferentiable (closedSmoothModelWithCorners 3) 𝓘(ℝ) f) :
    CovariantDerivative.chartTransportedLeviCivitaSection x (g.gradient f)
      =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x)]
    RicciFlow.RicciFlow.coordGradient (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) := by
  filter_upwards [GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x,
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hone hz
  have hG := CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric g.inner x hone
  have h := IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
    g x f hz (hf _)
  simpa only [RicciFlow.RicciFlow.coordGradient, anchorBlendedMetricFlow, hG] using h

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate gradient at the anchor is the intrinsic gradient. -/
theorem coordGradient_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hf : MDifferentiable (closedSmoothModelWithCorners 3) 𝓘(ℝ) f) :
    RicciFlow.RicciFlow.coordGradient (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f)
      (extChartAt (closedSmoothModelWithCorners 3) x x) = g.gradientAt f x := by
  apply (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0
    (extChartAt (closedSmoothModelWithCorners 3) x x)).inverse_apply_eq.mpr
  ext w
  have heq : ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
      =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x)]
      f ∘ (extChartAt (closedSmoothModelWithCorners 3) x).symm := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hz
    exact indicator_of_mem hz _
  rw [anchor_metric_apply, g.inner_gradientAt, extDerivFun_apply_chart (hf x), heq.fderiv_eq]


variable [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The intrinsic Laplacian of a chart-supported scalar equals the blended
coordinate Laplacian at the anchor. -/
theorem laplacianAt_eq_anchor_curvedLaplacian
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
    let hsymm := CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      GeodesicTransport.backgroundMetric_symm g.inner (fun y a b ↦ g.inner_symm y a b) x
    g.laplacianAt f x = CovariantDerivative.curvedLaplacian G
      (fun z ↦ RicciFlow.RicciFlow.metricBilin (G z))
      (fun z ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm z)
        (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 z))
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f)
      (extChartAt (closedSmoothModelWithCorners 3) x x) := by
  intro G hsymm
  have hG : G =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x)]
      CovariantDerivative.chartMetric g.inner x := by
    filter_upwards [GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x] with z hz
    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric g.inner x hz
  rw [ScalarGradientEvolution.laplacianAt_eq_anchor_derivatives g x f hs hf,
    RicciFlow.RicciFlow.curvedLaplacian_eq_raised_hessian_sum G hsymm
      (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0)]
  apply Finset.sum_congr rfl
  intro i _
  rw [anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt (fun _ ↦ g) x 0 i]
  simp only [RicciFlow.RicciFlow.christoffelClosedOp_apply,
    CovariantDerivative.christoffelFunctional, hG.self_of_nhds, hG.fderiv_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic Hessian at the anchor uses the blended Christoffel operator. -/
theorem hessianAt_eq_anchor_covariantHessianForm
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f)
    (v w : ClosedSmoothModel 3) :
    g.hessianAt f x v w = RicciFlow.RicciFlow.covariantHessianForm
      (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f)
      (extChartAt (closedSmoothModelWithCorners 3) x x) v w := by
  have hD : mfderivWithin 𝓘(ℝ, ClosedSmoothModel 3) (closedSmoothModelWithCorners 3)
      (extChartAt (closedSmoothModelWithCorners 3) x).symm
      (range (closedSmoothModelWithCorners 3))
      (extChartAt (closedSmoothModelWithCorners 3) x x) =
      ContinuousLinearMap.id ℝ (ClosedSmoothModel 3) := by
    have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (mem_extChartAt_source («I» := closedSmoothModelWithCorners 3) x)
    rw [mfderiv_extChartAt_self] at h
    simpa using h
  have h := IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
    g x (GeodesicTransport.cutoff (n := 3) x) (GeodesicTransport.cutoff_contDiff x)
    (GeodesicTransport.cutoff_tsupport x) (GeodesicTransport.cutoff_nonneg x)
    (GeodesicTransport.cutoff_le_one x) (mem_extChartAt_target x)
    (GeodesicTransport.cutoff_eventuallyEq_one x) f hs hf v w
  dsimp only at h
  rw [hD] at h
  change g.hessianAt f
    ((extChartAt (closedSmoothModelWithCorners 3) x).symm
      (extChartAt (closedSmoothModelWithCorners 3) x x)) v w = _ at h
  have hp := (extChartAt (closedSmoothModelWithCorners 3) x).left_inv (mem_extChartAt_source x)
  have he := congrArg (fun y : M ↦ g.hessianAt f y v w) hp
  exact he.symm.trans h

/-- Lowering the covariant derivative of the coordinate gradient identifies
it with the intrinsic covariant derivative at the anchor. -/
theorem covariantDeriv_coordGradient_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f)
    (v : ClosedSmoothModel 3) :
    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
    let q := extChartAt (closedSmoothModelWithCorners 3) x x
    fderiv ℝ (RicciFlow.RicciFlow.coordGradient G u) q v +
      RicciFlow.RicciFlow.christoffelClosedOp G q v
        (RicciFlow.RicciFlow.coordGradient G u q) = g.leviCivita (g.gradient f) x v := by
  intro G u q
  letI : NormedAddCommGroup (TangentSpace (closedSmoothModelWithCorners 3) x) :=
    inferInstanceAs (NormedAddCommGroup (ClosedSmoothModel 3))
  letI : NormedSpace ℝ (TangentSpace (closedSmoothModelWithCorners 3) x) :=
    inferInstanceAs (NormedSpace ℝ (ClosedSmoothModel 3))
  letI : FiniteDimensional ℝ (TangentSpace (closedSmoothModelWithCorners 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel 3))
  apply (LinearMap.BilinForm.toDual (g.metricBilinAt x)
    (g.metricBilinAt_nondegenerate x)).injective
  apply LinearMap.ext
  intro w
  change g.inner x _ w = g.hessianAt f x v w
  rw [hessianAt_eq_anchor_covariantHessianForm g x f hs hf]
  rw [← anchor_metric_apply]
  have hG : ContDiff ℝ ∞ G := CovariantDerivative.contDiff_blendedChartMetric
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
    g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
    (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
  have hsymm := CovariantDerivative.blendedChartMetric_symm
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
    GeodesicTransport.backgroundMetric_symm g.inner (fun y a b ↦ g.inner_symm y a b) x
  rw [RicciFlow.RicciFlow.covariantHessianForm_eq_covariantHessian G hsymm
    (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0)]
  exact RicciFlow.RicciFlow.g_covariantDeriv_coordGradient_eq_covariantHessian'
    G (hG.differentiable (by simp) q) hsymm
    (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0)
    (ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two x f hs hf) v w

end Poincare.IntrinsicBochnerScalarGradient
