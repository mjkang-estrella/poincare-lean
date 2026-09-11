import Poincare.Global.NormalizedFlowHausdorffPartitionStokes
import Poincare.Global.HamiltonChartDensityLocalDomination

/-!
# Open-chart data for closed Laplacian Stokes

The constructors below supply genuine chart measures and compactly supported
coordinate scalars. Coordinate coefficient identities remain explicit inputs
to the final partial constructor.
-/

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesProducer

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The full inverse-chart measure is the Riemannian measure on its open source. -/
theorem openChart_measure (g : ClosedSmoothRiemannianMetric n M) (p : M) :
    HausdorffChartDensityEquality g (extChartAt I p).target
      (inverseExtendedChartParametrization (n := n) p)
      (extChartAt I p).source (inverseChartPullbackVolumeDensity g p) := by
  have hrange : Set.range (inverseExtendedChartParametrization (n := n) p) =
      (extChartAt I p).source := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (extChartAt I p).map_target z.2
    · intro hx
      refine ⟨⟨extChartAt I p x, (extChartAt I p).map_source hx⟩, ?_⟩
      exact (extChartAt I p).left_inv hx
  simpa only [hrange] using inverseChart_hausdorffChartDensityEquality g p

/-- Finite Riemannian volume gives integrability of the density on the full chart. -/
theorem openChart_density_integrable (g : ClosedSmoothRiemannianMetric n M) (p : M) :
    Integrable (inverseChartPullbackVolumeDensity g p)
      (coordinateLebesgueMeasure (extChartAt I p).target) := by
  have hcont := continuous_inverseChartPullbackVolumeDensity g p
  have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
  have hmeas := (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable
  have hmass := congrArg (fun μ : Measure M ↦ μ univ) (openChart_measure g p)
  dsimp only at hmass
  rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hmass
  have hfinite :
      ∫⁻ z, ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) *
        inverseChartPullbackVolumeDensity g p z)
        ∂(coordinateLebesgueMeasure (extChartAt I p).target) ≠ (⊤ : ℝ≥0∞) := by
    rw [rawHausdorffCoordinateDensityMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hmass
    rw [hmass]
    letI := volumeMeasure_isFiniteMeasure g
    exact measure_ne_top (volumeMeasure g) _
  have hint := (lintegral_ofReal_ne_top_iff_integrable
    (hcont.const_mul (rawHausdorffLebesgueScale n : ℝ)).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ mul_nonneg hscale.le
      (inverseChartPullbackVolumeDensity_pos g p z).le)).mp hfinite
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint

/-- The compact finite chart cover has a smooth subordinate partition. -/
theorem exists_subordinate_partition (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ,
      ρ.IsSubordinate (fun i ↦ (extChartAt I (C.anchor i)).source) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ _
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
  rw [C.sources_cover]

/-- The coordinate scalar is extended by zero off the genuine target. -/
def coordinateScalar (p : M) (f : M → ℝ) : E → ℝ :=
  (extChartAt I p).target.indicator (fun z ↦ f ((extChartAt I p).symm z))

/-- A scalar supported inside a chart has a compactly supported coordinate extension. -/
theorem coordinateScalar_support (p : M) (f : M → ℝ)
    (hf : tsupport f ⊆ (extChartAt I p).source) :
    HasCompactSupport (coordinateScalar (n := n) p f) ∧
      tsupport (coordinateScalar (n := n) p f) ⊆ (extChartAt I p).target := by
  have hcompact : IsCompact ((extChartAt I p) '' tsupport f) :=
    (isClosed_tsupport f).isCompact.image_of_continuousOn
      ((continuousOn_extChartAt p).mono hf)
  have hsub : tsupport (coordinateScalar (n := n) p f) ⊆ (extChartAt I p) '' tsupport f := by
    apply closure_minimal _ hcompact.isClosed
    intro z hz
    by_cases hzt : z ∈ (extChartAt I p).target
    · refine ⟨(extChartAt I p).symm z, ?_, (extChartAt I p).right_inv hzt⟩
      apply subset_tsupport
      simpa only [Function.mem_support, coordinateScalar, indicator_of_mem hzt] using hz
    · exact False.elim (hz (indicator_of_notMem hzt _))
  exact ⟨hcompact.of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans (image_subset_iff.mpr fun x hx ↦ (extChartAt I p).map_source (hf hx))⟩

/-- Zero extension preserves C² regularity for scalars supported inside the source. -/
theorem coordinateScalar_contDiff_two (p : M) (f : M → ℝ)
    (hf : tsupport f ⊆ (extChartAt I p).source)
    (hreg : ContMDiff I 𝓘(ℝ) 2 f) :
    ContDiff ℝ 2 (coordinateScalar (n := n) p f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ (extChartAt I p).target
  · have hinv := (contMDiffOn_extChartAt_symm (n := 2) p z hz).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)
    have hcomp := (hreg.contMDiffAt.comp z hinv).contDiffAt
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
    exact indicator_of_mem hy _
  · have hout : z ∉ tsupport (coordinateScalar (n := n) p f) :=
      fun h ↦ hz ((coordinateScalar_support p f hf).2 h)
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

/-- A positive continuous density and a continuous coordinate divergence imply
continuity of the intrinsic Laplacian of a chart-supported C² scalar. -/
theorem laplacian_continuous_of_coordinate_divergence
    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
    (hf : tsupport f ⊆ (extChartAt I p).source)
    (hreg : ContMDiff I 𝓘(ℝ) 2 f)
    (w D : E → ℝ) (hw : Continuous w) (hD : Continuous D)
    (hwpos : ∀ z ∈ (extChartAt I p).target, 0 < w z)
    (hcoord : ∀ z : (extChartAt I p).target,
      w z * g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) = D z) :
    Continuous (fun x ↦ g.laplacianAt f x) := by
  have hformula (x : M) (hx : x ∈ (extChartAt I p).source) :
      g.laplacianAt f x = D (extChartAt I p x) / w (extChartAt I p x) := by
    let z : (extChartAt I p).target := ⟨extChartAt I p x, (extChartAt I p).map_source hx⟩
    have hinv : inverseExtendedChartParametrization (n := n) p z = x :=
      (extChartAt I p).left_inv hx
    apply (eq_div_iff (hwpos z z.2).ne').mpr
    simpa only [hinv, mul_comm] using hcoord z
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ (extChartAt I p).source
  · have hc := (continuousOn_extChartAt p x hx).continuousAt
      ((isOpen_extChartAt_source p).mem_nhds hx)
    have hquot := (hD.continuousAt.div hw.continuousAt
      (hwpos _ ((extChartAt I p).map_source hx)).ne').comp hc
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_source p).mem_nhds hx] with y hy
    exact hformula y hy
  · have hxt : x ∉ tsupport f := fun h ↦ hx (hf h)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
    calc
      g.laplacianAt f y = g.laplacianAt (fun _ : M ↦ (0 : ℝ)) y :=
        g.laplacianAt_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
          (g.mdifferentiableAt_gradient hreg.contMDiffAt)
          (g.mdifferentiableAt_gradient contMDiffAt_const)
      _ = 0 := g.laplacianAt_const 0 y

/-- The coefficient identities supply continuity, so measurability need not
be a separate input to the Stokes constructor. -/
theorem localizedLaplacian_continuous_of_coefficients
    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
    (hf : tsupport f ⊆ (extChartAt I p).source)
    (hreg : ContMDiff I 𝓘(ℝ) 2 f)
    (w : E → ℝ) (a : E → Fin n → Fin n → ℝ)
    (Γ : E → Fin n → Fin n → Fin n → ℝ)
    (hw : ContDiff ℝ 1 w) (ha : ∀ i j, ContDiff ℝ 1 (fun z ↦ a z i j))
    (hweight : ∀ z : (extChartAt I p).target,
      w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z)
    (hcompat : ∀ z : (extChartAt I p).target, ∀ j : Fin n,
      (∑ i : Fin n, fderiv ℝ (fun y ↦ w y * a y i j) z
        (EuclideanSpace.single i (1 : ℝ))) =
        w z * (-(∑ i : Fin n, ∑ k : Fin n, a z i k * Γ z j i k)))
    (hcoord : ∀ z : (extChartAt I p).target,
      g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
        christoffelCoordinateLaplacian a Γ (coordinateScalar (n := n) p f) z) :
    Continuous (fun x ↦ g.laplacianAt f x) := by
  let u := coordinateScalar (n := n) p f
  have hu : ContDiff ℝ 2 u := coordinateScalar_contDiff_two p f hf hreg
  let F := coordinateMetricFluxComponent w a u
  have hF (i : Fin n) : ContDiff ℝ 1 (F i) :=
    coordinateMetricFluxComponent_contDiff_one hw ha hu i
  apply laplacian_continuous_of_coordinate_divergence g p f hf hreg w
    (euclideanCoordinateDivergence F) hw.continuous
  · exact continuous_finsetSum _ fun i _ ↦
      ((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  · intro z hz
    rw [hweight ⟨z, hz⟩]
    have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
      exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
    exact mul_pos hscale (inverseChartPullbackVolumeDensity_pos g p ⟨z, hz⟩)
  · intro z
    have hdiv := euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
      (contractedChristoffel := fun y j ↦ -(∑ i : Fin n, ∑ k : Fin n, a y i k * Γ y j i k))
      (hw.differentiable one_ne_zero z)
      (fun i j ↦ (ha i j).differentiable one_ne_zero z)
      (fun j ↦ (coordinateDirectionalDerivative_contDiff_one hu j).differentiable one_ne_zero z)
      (hcompat z)
    rw [contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
      a Γ (fun y j ↦ -(∑ i : Fin n, ∑ k : Fin n, a y i k * Γ y j i k)) u z
      (fun _ ↦ rfl)] at hdiv
    rw [hcoord z]
    exact hdiv.symm

/-- A partial producer with every residual coefficient obligation stated as
an argument. Chart measures, partitioned scalar extensions and Laplacian
measurability are constructed rather than supplied. -/
def geometry_of_coordinate_coefficients
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ)
    (hreg : ContMDiff I 𝓘(ℝ) 2 f)
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ)
    (hρ : ρ.IsSubordinate (fun i ↦ (extChartAt I (C.anchor i)).source))
    (w : Fin C.chartCount → E → ℝ)
    (a : Fin C.chartCount → E → Fin n → Fin n → ℝ)
    (Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ)
    (hw : ∀ i, ContDiff ℝ 1 (w i))
    (ha : ∀ i j k, ContDiff ℝ 1 (fun z ↦ a i z j k))
    (hweight : ∀ i (z : (extChartAt I (C.anchor i)).target),
      w i z = (rawHausdorffLebesgueScale n : ℝ) *
        inverseChartPullbackVolumeDensity g (C.anchor i) z)
    (hcompat : ∀ i (z : (extChartAt I (C.anchor i)).target) (j : Fin n),
      (∑ k : Fin n, fderiv ℝ (fun y ↦ w i y * a i y k j) z
        (EuclideanSpace.single k (1 : ℝ))) =
        w i z * (-(∑ k : Fin n, ∑ l : Fin n, a i z k l * Γ i z j k l)))
    (hcoord : ∀ i (z : (extChartAt I (C.anchor i)).target),
      g.laplacianAt (fun x ↦ ρ i x * f x)
        (inverseExtendedChartParametrization (n := n) (C.anchor i) z) =
        christoffelCoordinateLaplacian (a i) (Γ i)
          (coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)) z) :
    FiniteSubordinateHausdorffLaplacianGeometry g f := by
  have hsupport (i : Fin C.chartCount) :
      tsupport (fun x ↦ ρ i x * f x) ⊆ (extChartAt I (C.anchor i)).source :=
    tsupport_mul_subset_left.trans (hρ i)
  have htwo : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hlocal (i : Fin C.chartCount) :
      ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
    ((ρ i).contMDiff.of_le htwo).mul hreg
  exact {
    chartCount := C.chartCount
    coordinateDomain := fun i ↦ (extChartAt I (C.anchor i)).target
    coordinateDomain_measurable := fun i ↦ (isOpen_extChartAt_target (C.anchor i)).measurableSet
    inverseChart := fun i ↦ inverseExtendedChartParametrization (n := n) (C.anchor i)
    inverseChart_measurable := fun i ↦
      (inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable
    chartRegion := fun i ↦ (extChartAt I (C.anchor i)).source
    chartRegion_isOpen := fun i ↦ isOpen_extChartAt_source (C.anchor i)
    density := fun i ↦ inverseChartPullbackVolumeDensity g (C.anchor i)
    density_nonneg := fun i ↦ Eventually.of_forall fun z ↦
      (inverseChartPullbackVolumeDensity_pos g (C.anchor i) z).le
    density_integrable := fun i ↦ openChart_density_integrable g (C.anchor i)
    chartMeasure := fun i ↦ openChart_measure g (C.anchor i)
    partition := ρ
    partition_subordinate := hρ
    f_contMDiff_two := hreg
    coordinateRepresentative := fun i ↦
      coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)
    coordinateRepresentative_eq := fun i z ↦ indicator_of_mem z.2 _
    coordinateRepresentative_contDiff_two := fun i ↦
      coordinateScalar_contDiff_two (C.anchor i) _ (hsupport i) (hlocal i)
    coordinateRepresentative_hasCompactSupport := fun i ↦
      (coordinateScalar_support (C.anchor i) _ (hsupport i)).1
    coordinateRepresentative_tsupport_subset_coordinateDomain := fun i ↦
      (coordinateScalar_support (C.anchor i) _ (hsupport i)).2
    weight := w
    weight_contDiff_one := hw
    weight_eq_density := hweight
    inverseMetric := a
    inverseMetric_contDiff_one := ha
    christoffel := Γ
    contractedChristoffel := fun i z j ↦ -(∑ k : Fin n, ∑ l : Fin n, a i z k l * Γ i z j k l)
    contractedChristoffel_eq := fun _ _ _ ↦ rfl
    density_inverseMetric_compatibility := hcompat
    intrinsicCoordinateLaplacian_eq := hcoord
    localizedLaplacian_aestronglyMeasurable := fun i ↦
      (localizedLaplacian_continuous_of_coefficients g (C.anchor i) _ (hsupport i) (hlocal i)
        (w i) (a i) (Γ i) (hw i) (ha i) (hweight i) (hcompat i) (hcoord i)).aestronglyMeasurable }

/-- Entrywise smoothness suffices for smoothness of a determinant on an open chart. -/
theorem contDiffOn_matrix_det (G : E → Matrix (Fin n) (Fin n) ℝ) (U : Set E)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U) :
    ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.mul contDiffOn_const
  apply contDiffOn_prod
  intro i _
  exact hG (σ i) i

end Poincare.ClosedLaplacianStokesProducer
