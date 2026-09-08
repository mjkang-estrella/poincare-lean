import Poincare.Global.HamiltonCompactFamilyInvariantContinuity
import Poincare.Global.HamiltonReactionCoreReduction
import Poincare.Global.HausdorffInverseChartGramContinuity
import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonFamilyVolumeMeasureContinuity

variable {n : ℕ} {M : Type u} {K : Type v}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [TopologicalSpace K]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/-- Value profiles at their own anchor give continuous intrinsic pairings
at each fixed manifold point and pair of tangent vectors. -/
theorem continuous_inner_of_thirdJetProfiles_continuous
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (a b : E) :
    Continuous (fun k ↦ (metric k).inner x a b) := by
  have h := (hjet (.value x a b)).comp
    (continuous_id.prodMk (continuous_const (y := extChartAt I x x)))
  simpa only [Function.comp_def, id_eq, metricEntryThirdJetProfile_value_anchor] using h

variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The pullback Gram matrix is continuous in the parameter at every genuine
coordinate, including coordinates outside the anchor's cutoff support. -/
theorem continuous_parameter_inverseChartPullbackGramMatrix
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (z : (extChartAt I x).target) :
    Continuous (fun k ↦ inverseChartPullbackGramMatrix (metric k) x z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_inner_of_thirdJetProfiles_continuous metric hjet _ _ _

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Every inverse-chart volume density is continuous in the metric parameter. -/
theorem continuous_parameter_inverseChartPullbackVolumeDensity
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (z : (extChartAt I x).target) :
    Continuous (fun k ↦ inverseChartPullbackVolumeDensity (metric k) x z) := by
  exact VolumeDensity.continuous_chartVolumeDensity
    (continuous_parameter_inverseChartPullbackGramMatrix metric hjet x z)

/-- On a fixed coordinate set where the anchor cutoff is one, the genuine
volume density is jointly continuous in the metric parameter and coordinate. -/
theorem continuous_inverseChartPullbackVolumeDensity_on_cutoffOne
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (S : Set E) (hS : S ⊆ (extChartAt I x).target)
    (hχ : ∀ z ∈ S, GeodesicTransport.cutoff (n := n) x z = 1) :
    Continuous (fun p : K × S ↦ inverseChartPullbackVolumeDensity
      (metric p.1) x ⟨p.2.1, hS p.2.2⟩) := by
  apply VolumeDensity.continuous_chartVolumeDensity
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hp : Continuous (fun p : K × S ↦ (p.1, (p.2 : E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h := (hjet (.value x (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))).comp hp
  apply h.congr
  intro p
  rw [inverseChartPullbackGramMatrix_eq_field]
  change CovariantDerivative.blendedChartMetric
      (GeodesicTransport.cutoff (n := n) x)
      (GeodesicTransport.backgroundMetric (n := n)) (metric p.1).inner x p.2.1 _ _ =
    CovariantDerivative.chartMetric (metric p.1).inner x p.2.1 _ _
  rw [CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    _ _ _ _ (hχ p.2.1 p.2.2)]

/-- Compact coordinate sets inside the cutoff-one region give continuous
weighted density integrals for an arbitrary topological parameter space.
Currying into continuous maps on the compact coordinate set gives uniform
control without a countability assumption on the parameter. -/
theorem continuous_integral_inverseChartPullbackVolumeDensity_on_compact
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (S : Set E) (hSc : IsCompact S)
    (hS : S ⊆ (extChartAt I x).target)
    (hχ : ∀ z ∈ S, GeodesicTransport.cutoff (n := n) x z = 1)
    (f : C(S, ℝ)) (A : Set S) :
    Continuous (fun k ↦ ∫ z : S, f z * inverseChartPullbackVolumeDensity
      (metric k) x ⟨z.1, hS z.2⟩ ∂(coordinateLebesgueMeasure S).restrict A) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let μ := coordinateLebesgueMeasure S
  letI : IsFiniteMeasure μ := ⟨by
    change Measure.comap ((↑) : S → E) volume univ < ⊤
    rw [(MeasurableEmbedding.subtype_coe hSc.measurableSet).comap_apply]
    simpa using hSc.measure_lt_top (μ := (volume : Measure E))⟩
  have hF : Continuous (fun p : K × S ↦ f p.2 * inverseChartPullbackVolumeDensity
      (metric p.1) x ⟨p.2.1, hS p.2.2⟩) :=
    (f.continuous.comp continuous_snd).mul
      (continuous_inverseChartPullbackVolumeDensity_on_cutoffOne metric hjet x S hS hχ)
  exact continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
    (fun _ : K ↦ (⟨μ.restrict A, inferInstance⟩ : FiniteMeasure S)) continuous_const
    (fun k z ↦ f z * inverseChartPullbackVolumeDensity
      (metric k) x ⟨z.1, hS z.2⟩) hF

/-- The landed area formula restricts to any compact coordinate set. -/
theorem compact_inverseChart_hausdorffChartDensityEquality
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (S : Set E) (hSc : IsCompact S) (hS : S ⊆ (extChartAt I x).target) :
    let ψ : S → M := fun z ↦ inverseExtendedChartParametrization x ⟨z.1, hS z.2⟩
    HausdorffChartDensityEquality g S ψ (range ψ)
      (fun z ↦ inverseChartPullbackVolumeDensity g x ⟨z.1, hS z.2⟩) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let T := (extChartAt I x).target
  let ι : S → T := Set.inclusion hS
  let ψ : T → M := inverseExtendedChartParametrization x
  have hι : Topology.IsEmbedding ι := Topology.IsEmbedding.inclusion hS
  have hψ : Topology.IsEmbedding ψ := inverseExtendedChartParametrization_isEmbedding x
  have hsmall : MeasurableSet (range (ψ ∘ ι)) :=
    (isCompact_range (hψ.continuous.comp hι.continuous)).measurableSet
  have hpre : ψ ⁻¹' range (ψ ∘ ι) = range ι := by
    ext z
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, hψ.injective hw⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
  have hsub : range (ψ ∘ ι) ⊆ range ψ := by
    rintro y ⟨z, rfl⟩
    exact ⟨ι z, rfl⟩
  change Measure.map (ψ ∘ ι)
      (rawHausdorffCoordinateDensityMeasure S
        (fun z ↦ inverseChartPullbackVolumeDensity g x (ι z))) =
    (volumeMeasure g).restrict (range (ψ ∘ ι))
  rw [← Measure.map_map hψ.continuous.measurable hι.continuous.measurable,
    map_rawHausdorffCoordinateDensityMeasure_inclusion
      (isOpen_extChartAt_target x).measurableSet hSc.measurableSet hS,
    ← hpre, ← Measure.restrict_map hψ.continuous.measurable hsmall]
  rw [show Measure.map ψ (rawHausdorffCoordinateDensityMeasure T
      (inverseChartPullbackVolumeDensity g x)) =
        (volumeMeasure g).restrict (range ψ) from
      inverseChart_hausdorffChartDensityEquality g x]
  exact Measure.restrict_restrict_of_subset hsub

/-- Volume integrals on a measurable piece of a compact cutoff-one chart
are continuous, with no regularity assumption on the boundary of the piece. -/
theorem continuous_integral_volumeMeasure_restrict_compact_chart
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (S : Set E) (hSc : IsCompact S)
    (hS : S ⊆ (extChartAt I x).target)
    (hχ : ∀ z ∈ S, GeodesicTransport.cutoff (n := n) x z = 1)
    (P : Set M) (hPm : MeasurableSet P)
    (hP : P ⊆ range (fun z : S ↦ inverseExtendedChartParametrization x ⟨z.1, hS z.2⟩))
    (f : C(M, ℝ)) :
    Continuous (fun k ↦ ∫ y in P, f y ∂volumeMeasure (metric k)) := by
  let ψ : S → M := fun z ↦ inverseExtendedChartParametrization x ⟨z.1, hS z.2⟩
  have hψ : Continuous ψ := (inverseExtendedChartParametrization_isEmbedding x).continuous.comp
    (continuous_subtype_val.subtype_mk fun z ↦ hS z.2)
  let c : ℝ := rawHausdorffLebesgueScale n
  let A : Set S := ψ ⁻¹' P
  let F : C(S, ℝ) := ⟨fun z ↦ c * f (ψ z), (f.continuous.comp hψ).const_mul c⟩
  have hcont := continuous_integral_inverseChartPullbackVolumeDensity_on_compact
    metric hjet x S hSc hS hχ F A
  apply hcont.congr
  intro k
  symm
  have hchart := compact_inverseChart_hausdorffChartDensityEquality (metric k) x S hSc hS
  change Measure.map ψ (rawHausdorffCoordinateDensityMeasure S
    (fun z ↦ inverseChartPullbackVolumeDensity (metric k) x ⟨z.1, hS z.2⟩)) =
      (volumeMeasure (metric k)).restrict (range ψ) at hchart
  rw [← Measure.restrict_restrict_of_subset hP, ← hchart,
    Measure.restrict_map hψ.measurable hPm,
    integral_map hψ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [rawHausdorffCoordinateDensityMeasure,
    restrict_withDensity (hPm.preimage hψ.measurable)]
  have hd : Continuous (fun z : S ↦ inverseChartPullbackVolumeDensity (metric k) x ⟨z.1, hS z.2⟩) :=
    (continuous_inverseChartPullbackVolumeDensity (metric k) x).comp
      (continuous_subtype_val.subtype_mk fun z ↦ hS z.2)
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((hd.const_mul c).measurable.ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z ↦ by
    have hn : 0 ≤ c * inverseChartPullbackVolumeDensity (metric k) x ⟨z.1, hS z.2⟩ :=
      mul_nonneg (by dsimp [c]; positivity)
        (inverseChartPullbackVolumeDensity_pos (metric k) x _).le
    dsimp only [F, ContinuousMap.coe_mk]
    rw [ENNReal.toReal_ofReal hn, smul_eq_mul]
    ring

end Poincare.HamiltonFamilyVolumeMeasureContinuity
