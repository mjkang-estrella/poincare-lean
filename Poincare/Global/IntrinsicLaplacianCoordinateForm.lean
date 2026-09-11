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

/-- A smooth local metric extension transports the intrinsic Hessian to the
ordinary second derivative with its Christoffel correction. -/
theorem hessianAt_eq_blended_chart_hessian
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (p : M)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχsupp : tsupport χ ⊆ (extChartAt I p).target)
    (hχ0 : ∀ q, 0 ≤ χ q) (hχ1 : ∀ q, χ q ≤ 1)
    {z : E} (hz : z ∈ (extChartAt I p).target)
    (hone : ∀ᶠ q in 𝓝 z, χ q = 1)
    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (v w : E) :
    let H := CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p
    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
      fderiv ℝ (fderiv ℝ u) z v w -
        fderiv ℝ u z (RicciFlow.RicciFlow.christoffelClosedOp H z v w) := by
  intro H u D
  have hpos (q : E) (hq : q ≠ 0) : 0 < innerSL ℝ q q := by
    simpa only [innerSL_apply_apply] using (real_inner_self_pos.mpr hq)
  have hsupp : ∀ q, χ q ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) q).IsInvertible := by
    intro q hq
    exact isInvertible_mfderivWithin_extChartAt_symm
      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hq)))
  have hH : ContDiff ℝ 1 H :=
    CovariantDerivative.contDiff_blendedChartMetric χ (innerSL ℝ) g.inner p
      (m := 1) (by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top) hχ hχsupp (g.contMDiff_inner.of_le (by norm_num))
  have hinv (q : E) : (H q).IsInvertible :=
    CovariantDerivative.metric_isInvertible H
      (CovariantDerivative.chartBilin χ (innerSL ℝ) g.inner p q)
      (CovariantDerivative.chartBilin_nondegenerate χ (innerSL ℝ) hpos g.inner
        (fun y v hv ↦ g.inner_pos y hv) p hχ0 hχ1 hsupp q) (fun _ _ ↦ rfl)
  have hsym (q a b : E) : H q a b = H q b a :=
    CovariantDerivative.blendedChartMetric_symm χ (innerSL ℝ)
      (fun a b : E ↦ real_inner_comm b a)
      g.inner (fun y a b ↦ g.inner_symm y a b) p q a b
  have hu : ContDiff ℝ 2 u :=
    ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
  let S := CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f)
  have heq : S =ᶠ[𝓝 z] RicciFlow.RicciFlow.coordGradient H u := by
    filter_upwards [hone, (isOpen_extChartAt_target p).mem_nhds hz] with q hq hqt
    have hg := transported_gradient_eq_coordGradient g p f hqt
      (hf.contMDiffAt.mdifferentiableAt two_ne_zero)
    have hHq : H q = CovariantDerivative.chartMetric g.inner p q :=
      CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
        χ (innerSL ℝ) g.inner p hq
    simpa only [RicciFlow.RicciFlow.coordGradient, hHq, S, u] using hg
  have hbridge :=
    LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
      g χ (innerSL ℝ) hpos p hχ0 hχ1 hsupp (hH.differentiable one_ne_zero)
      (fun a b : E ↦ real_inner_comm b a)
      ((extChartAt I p).map_target hz)
      (by simpa only [(extChartAt I p).right_inv hz] using hone)
      (show MDiffAtTangentField (g.gradient f) ((extChartAt I p).symm z) from
        g.mdifferentiableAt_gradient hf.contMDiffAt) (D v)
  dsimp only [CovariantDerivative.chartTransportedLeviCivitaValueAt,
    CovariantDerivative.chartTransportedLeviCivitaModelValue] at hbridge
  rw [(extChartAt I p).right_inv hz] at hbridge
  have hCD := congrArg (fun L : E →L[ℝ] E ↦ L v)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz)
  change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z)) (D v) = v at hCD
  have hbridge' : D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) =
      (LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
        ((extChartAt I p).symm z) (D v) :=
    (congrArg (fun a ↦ D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos
      g.inner (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) a)) hCD).symm.trans hbridge
  have hmodel :
      (CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
        (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v =
      fderiv ℝ (RicciFlow.RicciFlow.coordGradient H u) z v +
        RicciFlow.RicciFlow.christoffelClosedOp H z v
          (RicciFlow.RicciFlow.coordGradient H u z) := by
    rw [CovariantDerivative.chartLeviCivita, CovariantDerivative.modelLeviCivita_apply,
      ← RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt H _ _ (fun _ _ ↦ rfl)]
    rw [heq.fderiv_eq, heq.self_of_nhds]
  have hresult := RicciFlow.RicciFlow.g_covariantDeriv_coordGradient_eq_covariantHessian'
    H (hH.differentiable one_ne_zero z) hsym hinv hu v w
  rw [← RicciFlow.RicciFlow.covariantHessianForm_eq_covariantHessian H hsym hinv u z v w,
    RicciFlow.RicciFlow.covariantHessianForm_apply] at hresult
  rw [ClosedSmoothRiemannianMetric.hessianAt]
  change g.inner ((extChartAt I p).symm z)
    ((LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
      ((extChartAt I p).symm z) (D v)) (D w) = _
  rw [← hbridge']
  change CovariantDerivative.chartMetric g.inner p z
    ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) w = _
  rw [hmodel, ← CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    χ (innerSL ℝ) g.inner p hone.self_of_nhds]
  exact hresult

/-- The intrinsic Hessian in a genuine chart has the ordinary second derivative
and the connection of the genuine chart metric. -/
theorem hessianAt_eq_chart_derivatives
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (p : M)
    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {z : E} (hz : z ∈ (extChartAt I p).target) (v w : E) :
    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
      fderiv ℝ (fderiv ℝ u) z v w - fderiv ℝ u z
        (RicciFlow.RicciFlow.christoffelClosedOp
          (CovariantDerivative.chartMetric g.inner p) z v w) := by
  obtain ⟨χ, hχ, hχsupp, hone, hbounds⟩ :=
    ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
      (isCompact_singleton (x := z)) (isOpen_extChartAt_target p)
      (singleton_subset_iff.mpr hz)
  have heq : CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p =ᶠ[𝓝 z]
      CovariantDerivative.chartMetric g.inner p := by
    filter_upwards [hone z (mem_singleton z)] with q hq
    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
      χ (innerSL ℝ) g.inner p hq
  have h := hessianAt_eq_blended_chart_hessian g p χ hχ hχsupp
    (fun q ↦ (hbounds q).1) (fun q ↦ (hbounds q).2) hz
    (hone z (mem_singleton z)) f hs hf v w
  dsimp only at h ⊢
  simpa only [RicciFlow.RicciFlow.christoffelClosedOp_apply,
    CovariantDerivative.christoffelFunctional, heq.self_of_nhds, heq.fderiv_eq] using h

end Poincare.IntrinsicLaplacianCoordinateForm
