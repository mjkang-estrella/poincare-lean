import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
import Poincare.Global.DeTurckPrincipalIdentity

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.IntrinsicLaplacianCoordinateForm

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The intrinsic Hessian trace contracts with the inverse Gram matrix in any basis. -/
theorem laplacianAt_eq_inverseGram_hessian
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ (TM x)) :
    g.laplacianAt f x = ∑ i, ∑ j,
      (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [Poincare.laplacianAt_eq_sum_hessianAt_basis g f x b]
  apply Finset.sum_congr rfl
  intro i _
  rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
  change g.hessianDualAt f x (b i) (∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j • b j) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- In the inverse-chart frame the Laplacian uses the genuine inverse Gram field. -/
theorem laplacianAt_eq_chart_hessian
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (p : M)
    (z : (extChartAt I p).target) :
    g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
      ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
        g.hessianAt f ((extChartAt I p).symm z)
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
            (EuclideanSpace.basisFun (Fin n) ℝ i))
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
            (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p z.2
  have hG : g.metricMatrixInBasisAt ((extChartAt I p).symm z) b =
      inverseChartPullbackGramMatrixField g p z := by
    ext i j
    simp only [ClosedSmoothRiemannianMetric.metricMatrixInBasisAt_apply,
      ClosedSmoothRiemannianMetric.metricBilinAt_apply, b,
      ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
    rfl
  change g.laplacianAt f ((extChartAt I p).symm z) = _
  rw [laplacianAt_eq_inverseGram_hessian g f _ b, hG]
  simp only [b, ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]

/-- Pairing the transported intrinsic gradient with the chart metric gives the
ordinary differential of the coordinate scalar. -/
theorem chartMetric_transported_gradient
    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
    {z : E} (hz : z ∈ (extChartAt I p).target)
    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) (w : E) :
    CovariantDerivative.chartMetric g.inner p z
      (CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z) w =
      fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z w := by
  let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
  have hD : D.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm hz
  have heq : ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f =ᶠ[𝓝 z]
      f ∘ (extChartAt I p).symm := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
    exact indicator_of_mem hy _
  rw [heq.fderiv_eq, CovariantDerivative.chartMetric_apply,
    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
  change g.inner ((extChartAt I p).symm z)
    (D (D.inverse (g.gradient f ((extChartAt I p).symm z)))) (D w) = _
  rw [hD.self_apply_inverse]
  change g.inner ((extChartAt I p).symm z)
    (g.gradientAt f ((extChartAt I p).symm z)) (D w) = _
  rw [g.inner_gradientAt, extDerivFun_apply_fixed_chart ((extChartAt I p).map_target hz) hf,
    (extChartAt I p).right_inv hz]
  have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz
  have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hc
  change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z) (D w) = w at hw
  exact congrArg (fderiv ℝ (f ∘ (extChartAt I p).symm) z) hw

/-- The inverse-chart pullback of the intrinsic gradient is the coordinate gradient. -/
theorem transported_gradient_eq_coordGradient
    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
    {z : E} (hz : z ∈ (extChartAt I p).target)
    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) :
    CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z =
      RicciFlow.RicciFlow.coordGradient (CovariantDerivative.chartMetric g.inner p)
        (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z := by
  let G := CovariantDerivative.chartMetric g.inner p
  have hpos (v : E) (hv : v ≠ 0) : 0 < G z v v :=
    CovariantDerivative.chartMetric_posDef g.inner
      (fun y u hu ↦ g.inner_pos y hu) p
      (isInvertible_mfderivWithin_extChartAt_symm hz) hv
  have hnondeg : (RicciFlow.RicciFlow.metricBilin (G z)).Nondegenerate := by
    constructor
    · intro v hv
      by_contra h
      exact (ne_of_gt (hpos v h)) (hv v)
    · intro v hv
      by_contra h
      exact (ne_of_gt (hpos v h)) (hv v)
  have hinv : (G z).IsInvertible :=
    CovariantDerivative.metric_isInvertible G
      (RicciFlow.RicciFlow.metricBilin (G z)) hnondeg (fun _ _ ↦ rfl)
  symm
  apply hinv.inverse_apply_eq.mpr
  ext w
  exact (chartMetric_transported_gradient g p f hz hf w).symm

end Poincare.IntrinsicLaplacianCoordinateForm
