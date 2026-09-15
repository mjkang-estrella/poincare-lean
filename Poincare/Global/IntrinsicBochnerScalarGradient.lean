import Poincare.Global.ScalarGradientEvolution
import Poincare.Global.IntrinsicLaplacianCoordinateForm
import Poincare.Global.MetricFlowJointScalarTraceZoneBridge

noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
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
    (hf : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) f x) :
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
  rw [anchor_metric_apply, g.inner_gradientAt, extDerivFun_apply_chart hf, heq.fderiv_eq]


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

/-- The coordinate Hessian norm is the intrinsic metric trace of the squared
covariant derivative of the gradient, with the same basis and raised dual. -/
theorem coordCovariantHessNormSq_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    RicciFlow.RicciFlow.coordCovariantHessNormSq
      (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f)
      (extChartAt (closedSmoothModelWithCorners 3) x x) =
    ∑ i, g.inner x
      (g.leviCivita (g.gradient f) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
      (g.leviCivita (g.gradient f) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i))) := by
  unfold RicciFlow.RicciFlow.coordCovariantHessNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt (fun _ ↦ g) x 0 i,
    covariantDeriv_coordGradient_anchor g x f hs hf,
    covariantDeriv_coordGradient_anchor g x f hs hf, anchor_metric_apply]

/-- Trace the coordinate Hessian in the Euclidean basis using the inverse Gram matrix. -/
theorem curvedLaplacian_eq_inverseEntries_hessianForm
    (G : ClosedSmoothModel 3 → ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
    (hsymm : ∀ z v w, G z v w = G z w v)
    (hinv : ∀ z, (G z).IsInvertible) (f : ClosedSmoothModel 3 → ℝ)
    (z : ClosedSmoothModel 3) :
    CovariantDerivative.curvedLaplacian G (fun y ↦ RicciFlow.RicciFlow.metricBilin (G y))
      (fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y) (hinv y)) f z =
    ∑ i : Fin 3, ∑ j : Fin 3, DeTurckPrincipalSecondJet.inverseEntries (G z) i j *
      RicciFlow.RicciFlow.covariantHessianForm G f z
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let B := fun y ↦ RicciFlow.RicciFlow.metricBilin (G y)
  let hB := fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y) (hinv y)
  let A := (LinearMap.BilinForm.toDual (B z) (hB z)).symm.toLinearMap ∘ₗ
    CovariantDerivative.covariantHessianLin G B hB f z
  have hA (v : ClosedSmoothModel 3) :
      A v = (G z).inverse (RicciFlow.RicciFlow.covariantHessianForm G f z v) := by
    symm
    apply (hinv z).inverse_apply_eq.mpr
    ext w
    symm
    change B z ((LinearMap.BilinForm.toDual (B z) (hB z)).symm
      (CovariantDerivative.covariantHessianLin G B hB f z v)) w = _
    rw [LinearMap.BilinForm.apply_toDual_symm_apply]
    change CovariantDerivative.covariantHessian G B hB f z v w = _
    exact (RicciFlow.RicciFlow.covariantHessianForm_eq_covariantHessian
      G hsymm hinv f z v w).symm
  change LinearMap.trace ℝ (ClosedSmoothModel 3) A = _
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change b.coord i (A (b i)) = _
  rw [hA]
  exact IntrinsicLaplacianCoordinateForm.inverse_apply_coord (G z) (hinv z) (hsymm z)
    (RicciFlow.RicciFlow.covariantHessianForm G f z (b i)) i

/-- The intrinsic and blended coordinate Laplacians agree wherever the cutoff
is identically one on a neighborhood. -/
theorem laplacianAt_eq_curvedLaplacian_of_cutoff_one
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f)
    (z : (extChartAt (closedSmoothModelWithCorners 3) x).target)
    (hone : ∀ᶠ y in 𝓝 (z : ClosedSmoothModel 3), GeodesicTransport.cutoff (n := 3) x y = 1) :
    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
    let hsymm := CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      GeodesicTransport.backgroundMetric_symm g.inner (fun y a b ↦ g.inner_symm y a b) x
    g.laplacianAt f ((extChartAt (closedSmoothModelWithCorners 3) x).symm z) =
    CovariantDerivative.curvedLaplacian G (fun y ↦ RicciFlow.RicciFlow.metricBilin (G y))
      (fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y)
        (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 y))
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) z := by
  intro G hsymm
  have hG : G z = CovariantDerivative.chartMetric g.inner x z :=
    CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      g.inner x hone.self_of_nhds
  change g.laplacianAt f (inverseExtendedChartParametrization (n := 3) x z) = _
  rw [IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian g f x z,
    curvedLaplacian_eq_inverseEntries_hessianForm G hsymm
      (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hh := IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
    g x (GeodesicTransport.cutoff (n := 3) x) (GeodesicTransport.cutoff_contDiff x)
    (GeodesicTransport.cutoff_tsupport x) (GeodesicTransport.cutoff_nonneg x)
    (GeodesicTransport.cutoff_le_one x) z.2 hone f hs hf
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
  have hi : DeTurckPrincipalSecondJet.inverseEntries (G z) i j =
      (inverseChartPullbackGramMatrixField g x z)⁻¹ i j := by
    rw [hG]
    rfl
  rw [hi]
  exact congrArg (fun a : ℝ ↦ (inverseChartPullbackGramMatrixField g x z)⁻¹ i j * a) hh

/-- The intrinsic Laplacian and the blended coordinate Laplacian have equal
scalar germs at the anchor. This equality can be differentiated. -/
theorem laplacian_eventuallyEq_curvedLaplacian
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
    let hsymm := CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      GeodesicTransport.backgroundMetric_symm g.inner (fun y a b ↦ g.inner_symm y a b) x
    (fun z ↦ g.laplacianAt f ((extChartAt (closedSmoothModelWithCorners 3) x).symm z))
      =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x)]
    CovariantDerivative.curvedLaplacian G (fun y ↦ RicciFlow.RicciFlow.metricBilin (G y))
      (fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y)
        (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 y))
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) := by
  intro G hsymm
  filter_upwards [(GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x).eventually_nhds,
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hone hz
  exact laplacianAt_eq_curvedLaplacian_of_cutoff_one g x f hs hf ⟨z, hz⟩ hone

/-- Differentiating the Laplacian germ identifies its raised differential at
the anchor. The differentiability requirement is explicit. -/
theorem coordGradient_curvedLaplacian_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f)
    (hLap : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
      (fun y ↦ g.laplacianAt f y) x) :
    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
    let hsymm := CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      GeodesicTransport.backgroundMetric_symm g.inner (fun y a b ↦ g.inner_symm y a b) x
    let Δ := CovariantDerivative.curvedLaplacian G
      (fun y ↦ RicciFlow.RicciFlow.metricBilin (G y))
      (fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y)
        (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 y))
    RicciFlow.RicciFlow.coordGradient G
      (Δ (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f))
      (extChartAt (closedSmoothModelWithCorners 3) x x) =
      g.gradientAt (fun y ↦ g.laplacianAt f y) x := by
  intro G hsymm Δ
  have heq : ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x
      (fun y ↦ g.laplacianAt f y) =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x)]
      Δ (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) := by
    filter_upwards [laplacian_eventuallyEq_curvedLaplacian g x f hs hf,
      (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hz hzt
    rw [ClosedLaplacianStokesProducer.coordinateScalar, indicator_of_mem hzt]
    exact hz
  rw [← coordGradient_anchor g x (fun y ↦ g.laplacianAt f y) hLap]
  simp only [RicciFlow.RicciFlow.coordGradient, heq.fderiv_eq, G]

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The coordinate squared gradient norm represents the intrinsic squared
norm on a neighborhood of the anchor. -/
theorem gradientNormSq_eventuallyEq_coordGradNormSq
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hf : MDifferentiable (closedSmoothModelWithCorners 3) 𝓘(ℝ) f) :
    (fun z ↦ g.inner ((extChartAt (closedSmoothModelWithCorners 3) x).symm z)
      (g.gradientAt f ((extChartAt (closedSmoothModelWithCorners 3) x).symm z))
      (g.gradientAt f ((extChartAt (closedSmoothModelWithCorners 3) x).symm z)))
      =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x)]
    RicciFlow.RicciFlow.coordGradNormSq (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) := by
  filter_upwards [transported_gradient_eventuallyEq g x f hf,
    GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x,
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hgrad hone hz
  have hG := CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric g.inner x hone
  rw [RicciFlow.RicciFlow.coordGradNormSq, anchorBlendedMetricFlow, hG, ← hgrad]
  rw [CovariantDerivative.chartMetric_apply,
    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
  rw [(isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse]
  rfl

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A C³ scalar has a C² squared gradient norm. -/
theorem gradientNormSq_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric 3 M) (f : M → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) (x : M) :
    ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) x := by
  let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
  let q := extChartAt (closedSmoothModelWithCorners 3) x x
  let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
  have hu : ContDiffAt ℝ 3 u q := by
    have hi := (contMDiffOn_extChartAt_symm (n := 3) x q (mem_extChartAt_target x)).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    apply (hf.contMDiffAt.comp q hi).contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hz
    exact indicator_of_mem hz _
  have hGtop : ContDiff ℝ ∞ G := CovariantDerivative.contDiff_blendedChartMetric
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
    g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
    (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
  have hG : ContDiffAt ℝ 2 G q := (hGtop.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hInv : ContDiffAt ℝ 2 (fun z ↦ (G z).inverse) q :=
    (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 q).contDiffAt_map_inverse.comp q hG
  have hd : ContDiffAt ℝ 2 (RicciFlow.RicciFlow.coordGradient G u) q :=
    hInv.clm_apply (hu.fderiv_right (by norm_num))
  have hnorm : ContDiffAt ℝ 2 (RicciFlow.RicciFlow.coordGradNormSq G u) q :=
    (hG.clm_apply hd).clm_apply hd
  have hcomp := hnorm.contMDiffAt.comp x
    (contMDiffAt_extChartAt : ContMDiffAt (closedSmoothModelWithCorners 3)
      𝓘(ℝ, ClosedSmoothModel 3) 2 (extChartAt (closedSmoothModelWithCorners 3) x) x)
  apply hcomp.congr_of_eventuallyEq
  have heq := (continuousAt_extChartAt (I := closedSmoothModelWithCorners 3) x).eventually
    (gradientNormSq_eventuallyEq_coordGradNormSq g x f (hf.mdifferentiable (by norm_num)))
  filter_upwards [heq, (isOpen_extChartAt_source (I := closedSmoothModelWithCorners 3) x).mem_nhds
    (mem_extChartAt_source x)] with y hy hys
  rw [(extChartAt (closedSmoothModelWithCorners 3) x).left_inv hys] at hy
  exact hy

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Differentiation does not enlarge the topological support of a scalar's
squared gradient norm. -/
theorem gradientNormSq_tsupport_subset
    (g : ClosedSmoothRiemannianMetric 3 M) (f : M → ℝ) :
    tsupport (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) ⊆ tsupport f := by
  intro x hx
  by_contra hxf
  have heq := (notMem_tsupport_iff_eventuallyEq.mp hxf).eventually_nhds
  have hz : (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [heq] with y hy
    have hgrad := g.gradientAt_congr_of_eventuallyEq hy
    rw [hgrad]
    change g.inner y (g.gradientAt (fun _ ↦ 0) y) (g.gradientAt (fun _ ↦ 0) y) = 0
    rw [g.gradientAt_const]
    simp
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx

/-- Transport the Laplacian of the squared gradient norm for a chart-supported C³ scalar. -/
theorem laplacian_gradientNormSq_eq_anchor_curvedLaplacian
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) :
    let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
    let hsymm := CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
      GeodesicTransport.backgroundMetric_symm g.inner (fun y a b ↦ g.inner_symm y a b) x
    let Δ := CovariantDerivative.curvedLaplacian G
      (fun y ↦ RicciFlow.RicciFlow.metricBilin (G y))
      (fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y)
        (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 y))
    g.laplacianAt (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) x =
      Δ (RicciFlow.RicciFlow.coordGradNormSq G
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f))
        (extChartAt (closedSmoothModelWithCorners 3) x x) := by
  intro G hsymm Δ
  have heq : ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x
      (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y))
      =ᶠ[𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x)]
      RicciFlow.RicciFlow.coordGradNormSq G
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) := by
    filter_upwards [gradientNormSq_eventuallyEq_coordGradNormSq g x f
      (hf.mdifferentiable (by norm_num)),
      (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hz hzt
    rw [ClosedLaplacianStokesProducer.coordinateScalar, indicator_of_mem hzt]
    exact hz
  rw [laplacianAt_eq_anchor_curvedLaplacian g x _
    ((gradientNormSq_tsupport_subset g f).trans hs) (gradientNormSq_contMDiffAt_two g f hf)]
  change Δ (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x
    (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)))
    (extChartAt (closedSmoothModelWithCorners 3) x x) = _
  simp only [Δ, RicciFlow.RicciFlow.curvedLaplacian_eq_raised_hessian_sum G hsymm
    (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0),
    heq.fderiv_eq, heq.fderiv.fderiv_eq]

omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Zero extension of a chart-supported C³ scalar is C³. -/
theorem coordinateScalar_contDiff_three
    (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) :
    ContDiff ℝ 3 (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) x).target
  · have hinv := (contMDiffOn_extChartAt_symm (n := 3) x z hz).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
    apply (hf.contMDiffAt.comp z hinv).contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    exact indicator_of_mem hy _
  · have hout : z ∉ tsupport (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) :=
      fun h ↦ hz ((ClosedLaplacianStokesProducer.coordinateScalar_support x f hs).2 h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hout)

/-- The coordinate Laplacian of a C³ scalar is C¹ for a C³ invertible metric. -/
theorem curvedLaplacian_contDiffAt_one
    (G : ClosedSmoothModel 3 → ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
    (hG : ContDiff ℝ 3 G) (hsymm : ∀ z v w, G z v w = G z w v)
    (hinv : ∀ z, (G z).IsInvertible) (f : ClosedSmoothModel 3 → ℝ)
    (hf : ContDiff ℝ 3 f) (z : ClosedSmoothModel 3) :
    ContDiffAt ℝ 1
      (CovariantDerivative.curvedLaplacian G (fun y ↦ RicciFlow.RicciFlow.metricBilin (G y))
        (fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y) (hinv y)) f) z := by
  have hInv : ContDiffAt ℝ 1 (fun y ↦ (G y).inverse) z :=
    (hinv z).contDiffAt_map_inverse.comp z (hG.of_le (by norm_num)).contDiffAt
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 2) (by norm_num)).of_le (by norm_num)).contDiffAt
  have hdd : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) z :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)).contDiffAt
  change ContDiffAt ℝ 1 (fun y ↦ CovariantDerivative.curvedLaplacian G
    (fun y ↦ RicciFlow.RicciFlow.metricBilin (G y))
    (fun y ↦ RicciFlow.RicciFlow.metricBilin_nondeg (hsymm y) (hinv y)) f y) z
  simp_rw [RicciFlow.RicciFlow.curvedLaplacian_eq_raised_hessian_sum G hsymm hinv]
  apply ContDiffAt.sum
  intro i _
  have hr := hInv.clm_apply (contDiffAt_const (c := LinearMap.toContinuousLinearMap
    ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
  have hΓ := (RicciFlow.RicciFlow.contDiffAt_christoffelClosedOp G (x := z) hG hinv
    ((Module.finBasis ℝ (ClosedSmoothModel 3)) i)).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hswap (y : ClosedSmoothModel 3) :
      RicciFlow.RicciFlow.christoffelClosedOp G y
        ((G y).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
        ((Module.finBasis ℝ (ClosedSmoothModel 3)) i) =
      RicciFlow.RicciFlow.christoffelClosedOp G y
        ((Module.finBasis ℝ (ClosedSmoothModel 3)) i)
        ((G y).inverse (LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i))) :=
    RicciFlow.RicciFlow.christoffelClosedOp_symm
      (hG.differentiable (by norm_num) y) hsymm _ _
  simp_rw [hswap]
  exact ((hdd.clm_apply hr).clm_apply contDiffAt_const).sub (hd.clm_apply (hΓ.clm_apply hr))

/-- C³ scalar regularity supplies differentiability of the intrinsic Laplacian
at the anchor of a supporting chart. -/
theorem laplacianAt_mdifferentiableAt_of_supported_contMDiff_three
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) :
    MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
      (fun y ↦ g.laplacianAt f y) x := by
  let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
  let hsymm := CovariantDerivative.blendedChartMetric_symm
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
    GeodesicTransport.backgroundMetric_symm g.inner (fun y a b ↦ g.inner_symm y a b) x
  have hG : ContDiff ℝ ∞ G := CovariantDerivative.contDiff_blendedChartMetric
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
    g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
    (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
  have hc := curvedLaplacian_contDiffAt_one G (hG.of_le (WithTop.coe_le_coe.mpr le_top))
    hsymm (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0) _
    (coordinateScalar_contDiff_three x f hs hf) (extChartAt (closedSmoothModelWithCorners 3) x x)
  have hcomp := hc.contMDiffAt.comp x
    (contMDiffAt_extChartAt : ContMDiffAt (closedSmoothModelWithCorners 3)
      𝓘(ℝ, ClosedSmoothModel 3) 1 (extChartAt (closedSmoothModelWithCorners 3) x) x)
  apply (hcomp.congr_of_eventuallyEq ?_).mdifferentiableAt one_ne_zero
  have heq := (continuousAt_extChartAt (I := closedSmoothModelWithCorners 3) x).eventually
    (laplacian_eventuallyEq_curvedLaplacian g x f hs (hf.of_le (by norm_num)))
  filter_upwards [heq, (isOpen_extChartAt_source (I := closedSmoothModelWithCorners 3) x).mem_nhds
    (mem_extChartAt_source x)] with y hy hys
  rw [(extChartAt (closedSmoothModelWithCorners 3) x).left_inv hys] at hy
  exact hy

/-- Intrinsic Bochner for a C³ scalar supported in the anchor chart. -/
theorem bochner_of_chart_supported
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) :
    g.laplacianAt (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) x =
      2 * (∑ i, g.inner x
        (g.leviCivita (g.gradient f) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
        (g.leviCivita (g.gradient f) x
          (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))) +
      2 * g.inner x (g.gradientAt f x) (g.gradientAt (fun y ↦ g.laplacianAt f y) x) +
      2 * g.ricciAt x (g.gradientAt f x) (g.gradientAt f x) := by
  have hf2 := hf.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  have hd := (hf x).mdifferentiableAt (by norm_num : (3 : ℕ∞ω) ≠ 0)
  have hLap := laplacianAt_mdifferentiableAt_of_supported_contMDiff_three g x f hs hf
  have h := ScalarGradientEvolution.bochner_anchorBlendedMetric g x
    (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f)
    (coordinateScalar_contDiff_three x f hs hf)
  dsimp only at h
  rw [coordCovariantHessNormSq_anchor g x f hs hf2,
    coordGradient_curvedLaplacian_anchor g x f hs hf2 hLap,
    coordGradient_anchor g x f hd, anchor_metric_apply] at h
  exact (laplacian_gradientNormSq_eq_anchor_curvedLaplacian g x f hs hf).trans h

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Every C³ scalar has a chart-supported C³ representative of its germ. -/
theorem exists_chart_supported_scalar_germ
    (x : M) (f : M → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) :
    ∃ u : M → ℝ, tsupport u ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source ∧
      ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 u ∧ u =ᶠ[𝓝 x] f := by
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (closedSmoothModelWithCorners 3)
    (isOpen_extChartAt_source (I := closedSmoothModelWithCorners 3) x).isClosed_compl
    (isClosed_singleton (x := x))
    (disjoint_compl_left_iff_subset.mpr (singleton_subset_iff.mpr (mem_extChartAt_source x)))
    (n := 3)
  have hs : tsupport (fun y ↦ χ y) ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source := by
    intro y hy
    by_contra hys
    have hz : (fun y ↦ χ y) =ᶠ[𝓝 y] 0 := hzero.filter_mono (nhds_le_nhdsSet hys)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hy
  refine ⟨(fun y ↦ χ y * f y), tsupport_mul_subset_left.trans hs, χ.contMDiff.smul hf, ?_⟩
  have hone' : ∀ᶠ y in 𝓝 x, χ y = 1 := hone.filter_mono (nhds_le_nhdsSet (mem_singleton x))
  filter_upwards [hone'] with y hy
  simp only [hy, one_mul]

/-- Intrinsic Bochner for a C³ scalar on the closed smooth manifold. -/
theorem bochner
    (g : ClosedSmoothRiemannianMetric 3 M) (f : M → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) (x : M) :
    g.laplacianAt (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) x =
      2 * (∑ i, g.inner x
        (g.leviCivita (g.gradient f) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
        (g.leviCivita (g.gradient f) x
          (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))) +
      2 * g.inner x (g.gradientAt f x) (g.gradientAt (fun y ↦ g.laplacianAt f y) x) +
      2 * g.ricciAt x (g.gradientAt f x) (g.gradientAt f x) := by
  obtain ⟨u, hs, hu, heq⟩ := exists_chart_supported_scalar_germ x f hf
  have hgrad : ∀ᶠ y in 𝓝 x, g.gradient u y = g.gradient f y := by
    filter_upwards [heq.eventually_nhds] with y hy
    exact g.gradientAt_congr_of_eventuallyEq hy
  have hnorm : (fun y ↦ g.inner y (g.gradientAt u y) (g.gradientAt u y)) =ᶠ[𝓝 x]
      (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) := by
    filter_upwards [hgrad] with y hy
    exact congrArg (fun v ↦ g.inner y v v) hy
  have hLap : (fun y ↦ g.laplacianAt u y) =ᶠ[𝓝 x] (fun y ↦ g.laplacianAt f y) := by
    filter_upwards [heq.eventually_nhds] with y hy
    exact g.laplacianAt_congr_of_eventuallyEq hy
      (g.mdifferentiableAt_gradient ((hu.of_le (by norm_num)) y))
      (g.mdifferentiableAt_gradient ((hf.of_le (by norm_num)) y))
  have hCov : g.leviCivita (g.gradient u) x = g.leviCivita (g.gradient f) x :=
    g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (g.mdifferentiableAt_gradient ((hu.of_le (by norm_num)) x))
      (g.mdifferentiableAt_gradient ((hf.of_le (by norm_num)) x)) univ_mem hgrad
  have hnormLap := g.laplacianAt_congr_of_eventuallyEq hnorm
    (g.mdifferentiableAt_gradient (gradientNormSq_contMDiffAt_two g u hu x))
    (g.mdifferentiableAt_gradient (gradientNormSq_contMDiffAt_two g f hf x))
  have h := bochner_of_chart_supported g x u hs hu
  rw [hnormLap, hCov, g.gradientAt_congr_of_eventuallyEq heq,
    g.gradientAt_congr_of_eventuallyEq hLap] at h
  exact h

/-- A C³ scalar has a differentiable intrinsic Laplacian at every point. -/
theorem laplacianAt_mdifferentiableAt_of_contMDiff_three
    (g : ClosedSmoothRiemannianMetric 3 M) (f : M → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) (x : M) :
    MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
      (fun y ↦ g.laplacianAt f y) x := by
  obtain ⟨u, hs, hu, heq⟩ := exists_chart_supported_scalar_germ x f hf
  have hLap : (fun y ↦ g.laplacianAt u y) =ᶠ[𝓝 x] (fun y ↦ g.laplacianAt f y) := by
    filter_upwards [heq.eventually_nhds] with y hy
    exact g.laplacianAt_congr_of_eventuallyEq hy
      (g.mdifferentiableAt_gradient ((hu.of_le (by norm_num)) y))
      (g.mdifferentiableAt_gradient ((hf.of_le (by norm_num)) y))
  exact (laplacianAt_mdifferentiableAt_of_supported_contMDiff_three g x u hs hu).congr_of_eventuallyEq
    hLap.symm

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Intrinsic scalar curvature and the anchor-chart curvature trace agree as
joint space-time germs, independently of the regularity order. -/
theorem scalar_joint_eventuallyEq_anchorTrace
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) (x : M) :
    (fun p : ℝ × ClosedSmoothModel 3 ↦
      (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      =ᶠ[𝓝 (t, extChartAt (closedSmoothModelWithCorners 3) x x)]
      Function.uncurry (anchorChartScalarTraceFlow gt x) := by
  have ht : ∀ᶠ p : ℝ × ClosedSmoothModel 3 in
      𝓝 (t, extChartAt (closedSmoothModelWithCorners 3) x x),
      p.2 ∈ (extChartAt (closedSmoothModelWithCorners 3) x).target :=
    continuousAt_snd.eventually ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hone : ∀ᶠ p : ℝ × ClosedSmoothModel 3 in
      𝓝 (t, extChartAt (closedSmoothModelWithCorners 3) x x),
      ∀ᶠ z in 𝓝 p.2, GeodesicTransport.cutoff (n := 3) x z = 1 := by
    have hsnd : ContinuousAt (fun p : ℝ × ClosedSmoothModel 3 ↦ p.2)
        (t, extChartAt (closedSmoothModelWithCorners 3) x x) := continuousAt_snd
    have hc : ∀ᶠ y in 𝓝 (extChartAt (closedSmoothModelWithCorners 3) x x),
        ∀ᶠ z in 𝓝 y, GeodesicTransport.cutoff (n := 3) x z = 1 :=
      (GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x).eventually_nhds
    exact hsnd.eventually hc
  filter_upwards [ht, hone] with p hp hχ
  exact (anchorChartScalarTraceFlow_eq_scalarAt_zone gt x p.1 hp hχ).symm

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The landed joint C³ metric-entry producer supplies actual joint C¹ scalar
curvature through the chart-zone identity. -/
theorem scalar_jointContDiffAt_one_of_metricEntries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t x 3) :
    ContDiffAt ℝ 1
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) :=
  (anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries hJoint).congr_of_eventuallyEq
    (scalar_joint_eventuallyEq_anchorTrace gt t x)

section HigherRegularity

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Taking a spatial derivative loses one joint derivative. -/
theorem spatial_fderiv_jointContDiffAt
    (F : ℝ → V → W) (t : ℝ) (z : V) (k : ℕ)
    (hF : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (Function.uncurry F) (t, z)) :
    ContDiffAt ℝ k (fun p : ℝ × V ↦ fderiv ℝ (F p.1) p.2) (t, z) := by
  have hd := hF.fderiv_right (m := (k : ℕ∞ω)) (by rfl)
  have hc := hd.clm_comp
    (contDiffAt_const (c := ContinuousLinearMap.inr ℝ ℝ V))
  have hnear : ∀ᶠ p in 𝓝 (t, z), DifferentiableAt ℝ (Function.uncurry F) p :=
    ((hF.of_le (show (1 : ℕ∞ω) ≤ (k : ℕ∞ω) + 1 by exact le_add_self)).eventually
      (by norm_num)).mono fun _ hp ↦ hp.differentiableAt one_ne_zero
  apply hc.congr_of_eventuallyEq
  filter_upwards [hnear] with p hp
  rcases p with ⟨s, y⟩
  have hs : HasFDerivAt (fun z' : V ↦ Function.uncurry F (s, z'))
      ((fderiv ℝ (Function.uncurry F) (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ V)) y :=
    hp.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  exact hs.fderiv

end HigherRegularity

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Joint metric regularity survives chart blending near the anchor. -/
theorem blendedMetric_jointContDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    {k : ℕ∞ω} (hJoint : MetricEntriesJointContDiffAt gt t x k) :
    ContDiffAt ℝ k (Function.uncurry (anchorBlendedMetricFlow gt x))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) :=
  (anchorChartMetricFlow_jointContDiffAt_of_metricEntries hJoint).congr_of_eventuallyEq
    (anchorBlendedMetricFlow_eventuallyEq_anchorChartMetricFlow gt t x)

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The Christoffel field loses one derivative from the joint metric entries. -/
theorem christoffel_jointContDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (k : ℕ) (hJoint : MetricEntriesJointContDiffAt gt t x ((k : ℕ∞ω) + 1)) :
    ContDiffAt ℝ k (Function.uncurry (anchorChartChristoffelFieldFlow gt x))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) := by
  let q := extChartAt (closedSmoothModelWithCorners 3) x x
  have hg := blendedMetric_jointContDiffAt hJoint
  have hi : ContDiffAt ℝ k
      (fun p : ℝ × ClosedSmoothModel 3 ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t, q) :=
    (anchorBlendedMetricFlow_isInvertible gt x t q).contDiffAt_map_inverse.comp
      (t, q) (hg.of_le (by exact le_self_add))
  have hd := spatial_fderiv_jointContDiffAt (anchorBlendedMetricFlow gt x) t q k hg
  apply contDiffAt_clm_path_of_apply
  intro u
  apply contDiffAt_clm_path_of_apply
  intro v
  have hk : ContDiffAt ℝ k
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        jointChristoffelCovectorAt (anchorBlendedMetricFlow gt x) p.1 p.2 v u) (t, q) := by
    apply contDiffAt_clm_path_of_apply
    intro w
    have h₁ := ((hd.clm_apply (contDiffAt_const (c := v))).clm_apply
      (contDiffAt_const (c := u))).clm_apply (contDiffAt_const (c := w))
    have h₂ := ((hd.clm_apply (contDiffAt_const (c := u))).clm_apply
      (contDiffAt_const (c := v))).clm_apply (contDiffAt_const (c := w))
    have h₃ := ((hd.clm_apply (contDiffAt_const (c := w))).clm_apply
      (contDiffAt_const (c := v))).clm_apply (contDiffAt_const (c := u))
    simpa [jointChristoffelCovectorAt, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.smul_apply] using ((h₁.add h₂).sub h₃).const_smul (1 / 2 : ℝ)
  simpa only [Function.uncurry, anchorChartChristoffelFieldFlow_apply,
    anchorChartChristoffelFlow_apply_eq_inverse_koszul] using hi.clm_apply hk

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Joint curvature regularity loses two derivatives from metric entries. -/
theorem curvature_jointContDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (k : ℕ) (hJoint : MetricEntriesJointContDiffAt gt t x ((k : ℕ∞ω) + 2))
    (u v w : ClosedSmoothModel 3) :
    ContDiffAt ℝ k
      (fun p : ℝ × ClosedSmoothModel 3 ↦ anchorChartCurvatureFlow gt x p.1 p.2 u v w)
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) := by
  let q := extChartAt (closedSmoothModelWithCorners 3) x x
  let Γ := anchorChartChristoffelFieldFlow gt x
  have hΓ : ContDiffAt ℝ ((k : ℕ∞ω) + 1) (Function.uncurry Γ) (t, q) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
      christoffel_jointContDiffAt (k + 1) (by simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hJoint)
  have hlow := hΓ.of_le (show (k : ℕ∞ω) ≤ (k : ℕ∞ω) + 1 from le_self_add)
  have hvw := (hΓ.clm_apply (contDiffAt_const (c := v))).clm_apply (contDiffAt_const (c := w))
  have huw := (hΓ.clm_apply (contDiffAt_const (c := u))).clm_apply (contDiffAt_const (c := w))
  have hdvw := spatial_fderiv_jointContDiffAt (fun s y ↦ Γ s y v w) t q k hvw
  have hduw := spatial_fderiv_jointContDiffAt (fun s y ↦ Γ s y u w) t q k huw
  have hu := hlow.clm_apply (contDiffAt_const (c := u))
  have hv := hlow.clm_apply (contDiffAt_const (c := v))
  have hw : ContDiffAt ℝ k (fun _ : ℝ × ClosedSmoothModel 3 ↦ w) (t, q) := contDiffAt_const
  have hr := (((hdvw.clm_apply (contDiffAt_const (c := u))).sub
    (hduw.clm_apply (contDiffAt_const (c := v)))).add
    (hu.clm_apply (hv.clm_apply hw))).sub (hv.clm_apply (hu.clm_apply hw))
  apply hr.congr_of_eventuallyEq
  have hnear : ∀ᶠ p in 𝓝 (t, q), DifferentiableAt ℝ (Function.uncurry Γ) p :=
    ((hΓ.of_le (show (1 : ℕ∞ω) ≤ (k : ℕ∞ω) + 1 from le_add_self)).eventually
      (by norm_num)).mono fun _ hp ↦ hp.differentiableAt one_ne_zero
  filter_upwards [hnear] with p hp
  rcases p with ⟨s, y⟩
  have hs : DifferentiableAt ℝ (Γ s) y := by
    have hpath : DifferentiableAt ℝ (fun y' : ClosedSmoothModel 3 ↦ (s, y')) y :=
      (hasFDerivAt_prodMk_right s y).differentiableAt
    exact DifferentiableAt.comp (𝕜 := ℝ) (f := fun y' ↦ (s, y'))
      (g := Function.uncurry Γ) (x := y) hp hpath
  exact ChartCurvatureBridge.chartCurvatureOf_eq_fderiv_apply hs u v w

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The inverse-metric curvature trace has the same regularity as curvature. -/
theorem scalarTrace_jointContDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (k : ℕ) (hJoint : MetricEntriesJointContDiffAt gt t x ((k : ℕ∞ω) + 2)) :
    ContDiffAt ℝ k (Function.uncurry (anchorChartScalarTraceFlow gt x))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) := by
  classical
  let q := extChartAt (closedSmoothModelWithCorners 3) x x
  let b := Module.finBasis ℝ (ClosedSmoothModel 3)
  have hi : ContDiffAt ℝ k
      (fun p : ℝ × ClosedSmoothModel 3 ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t, q) :=
    (anchorBlendedMetricFlow_isInvertible gt x t q).contDiffAt_map_inverse.comp (t, q)
      ((blendedMetric_jointContDiffAt hJoint).of_le (by exact le_self_add))
  unfold anchorChartScalarTraceFlow
  dsimp only
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hi' := (contDiffAt_const (c := LinearMap.toContinuousLinearMap (b.coord j))).clm_apply
    (hi.clm_apply (contDiffAt_const (c := LinearMap.toContinuousLinearMap (b.coord i))))
  apply hi'.mul
  unfold anchorChartRicciEntryFlow
  dsimp only
  apply ContDiffAt.sum
  intro l _
  exact (contDiffAt_const (c := LinearMap.toContinuousLinearMap (b.coord l))).clm_apply
    (curvature_jointContDiffAt k hJoint (b l) (b i) (b j))

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Intrinsic scalar curvature inherits the joint curvature-trace regularity. -/
theorem scalar_jointContDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (k : ℕ) (hJoint : MetricEntriesJointContDiffAt gt t x ((k : ℕ∞ω) + 2)) :
    ContDiffAt ℝ k
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) :=
  (scalarTrace_jointContDiffAt k hJoint).congr_of_eventuallyEq
    (scalar_joint_eventuallyEq_anchorTrace gt t x)

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Restrict joint scalar regularity to a time slice and return to the manifold. -/
theorem scalar_contMDiffAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (k : ℕ) (hJoint : MetricEntriesJointContDiffAt gt t x ((k : ℕ∞ω) + 2)) :
    ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) k
      (fun y ↦ (gt t).scalarAt y) x := by
  have hj := scalar_jointContDiffAt k hJoint
  have hs : ContDiffAt ℝ k
      (fun z : ClosedSmoothModel 3 ↦
        (gt t).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm z))
      (extChartAt (closedSmoothModelWithCorners 3) x x) :=
    hj.comp _ (contDiffAt_const.prodMk contDiffAt_id)
  have hc := hs.contMDiffAt.comp x
    (contMDiffAt_extChartAt : ContMDiffAt (closedSmoothModelWithCorners 3)
      𝓘(ℝ, ClosedSmoothModel 3) k (extChartAt (closedSmoothModelWithCorners 3) x) x)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := closedSmoothModelWithCorners 3) x).mem_nhds
    (mem_extChartAt_source x)] with y hy
  simp only [Function.comp_apply, (extChartAt (closedSmoothModelWithCorners 3) x).left_inv hy]

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Fourth-order joint metric entries give joint C² scalar curvature. -/
theorem scalar_jointContDiffAt_two_of_metricEntries_four
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hJoint4 : ∀ t y, MetricEntriesJointContDiffAt gt t y 4) (t : ℝ) (x : M) :
    ContDiffAt ℝ 2
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) :=
  scalar_jointContDiffAt 2 (hJoint4 t x)

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Fifth-order joint metric entries give the spatial C³ scalar required by Bochner. -/
theorem scalar_contMDiff_three_of_metricEntries_five
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hJoint5 : ∀ t y, MetricEntriesJointContDiffAt gt t y 5) (t : ℝ) :
    ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 (fun y ↦ (gt t).scalarAt y) :=
  fun x ↦ scalar_contMDiffAt_of_metricEntries 3 (hJoint5 t x)

/-- Fifth-order joint entries supply both extra scalar hypotheses of the time theorem. -/
theorem scalarRegularity_of_metricEntries_five
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hJoint5 : ∀ t y, MetricEntriesJointContDiffAt gt t y 5) (t : ℝ) (x : M) :
    ContDiffAt ℝ 2
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) ∧
    MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
      (fun y ↦ (gt t).laplacianAt (fun z ↦ (gt t).scalarAt z) y) x := by
  exact ⟨scalar_jointContDiffAt_two_of_metricEntries_four
      (fun s y ↦ (hJoint5 s y).of_le (by norm_num)) t x,
    laplacianAt_mdifferentiableAt_of_contMDiff_three (gt t) _
      (scalar_contMDiff_three_of_metricEntries_five hJoint5 t) x⟩

end Poincare.IntrinsicBochnerScalarGradient
