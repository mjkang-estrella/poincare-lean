import Poincare.ProofProgress.SurgeryPerelmanPackageLayer

/-!
# Grounded Perelman singularity control

The legacy aggregate singularity-control payload permits arbitrary nested
regions, including empty ones. This module retains the actual classification
chain and indexes every pointed rescaling by a spacetime point whose Ricci
tensor norm exceeds a positive threshold. The legacy regions are then fixed to
the spatial projection of those points and the range of the pointed-rescaling
basepoint map.

The high-curvature predicate below uses the norm of the implemented Ricci
tensor `ricci_tensor_at_time_of_ricci_flow_data`. Identifying this norm with a
full Riemann-curvature norm in dimension three remains future work; this module
does not claim or assume that identification.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace Poincare

universe u

/-- The operator norm of the implemented Ricci tensor at a spacetime point,
using the Riemannian norm supplied by that time slice of the flow metric. -/
noncomputable def perelmanRicciTensorNormAt
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (t : ℝ) (x : M) : ℝ := by
  let g := metric_at_time_of_ricci_flow_data flow t
  letI : RiemannianBundle
      (fun y : M => TangentSpace ThreeManifoldModelWithCorners y) :=
    ⟨g.toRiemannianMetric⟩
  letI : NormedAddCommGroup
      (TangentSpace ThreeManifoldModelWithCorners x) :=
    inferInstance
  letI : NormedSpace ℝ
      (TangentSpace ThreeManifoldModelWithCorners x) :=
    inferInstance
  exact ‖ricci_tensor_at_time_of_ricci_flow_data flow t x‖

/-- A spacetime point whose implemented Ricci tensor norm exceeds the selected
positive high-curvature threshold. -/
abbrev PerelmanHighRicciCurvatureSpacetimePoint
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (threshold : ℝ) :=
  {p : ℝ × M //
    threshold ≤
      perelmanRicciTensorNormAt flow p.1 p.2}

namespace SingularityModelClassificationPayloadSource

/-- The pointed-rescaling payload at the base of the selected singularity
classification chain. -/
abbrev pointedRescalingPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (source : SingularityModelClassificationPayloadSource flow) :=
  source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.curvatureNormalizationSource.pointedRescalingSource.payload

/-- The no-local-collapsing contradiction payload in the same classification
chain. -/
abbrev noLocalCollapsingContradictionSetupPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (source : SingularityModelClassificationPayloadSource flow) :=
  source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.curvatureNormalizationSource.pointedRescalingSource.limitExtractionSource.hamiltonCompactnessSource.collapsedBallBlowupSource.noLocalCollapsingContradictionSetupSource.payload

/-- The reduced-volume nonincreasing payload in the same classification
chain. -/
abbrev reducedVolumeNonincreasingPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (source : SingularityModelClassificationPayloadSource flow) :=
  source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.curvatureNormalizationSource.pointedRescalingSource.limitExtractionSource.hamiltonCompactnessSource.collapsedBallBlowupSource.noLocalCollapsingContradictionSetupSource.kappaNoncollapsingFromReducedVolumeSource.reducedVolumeNonincreasingSource.payload

/-- The positive reduced-volume lower-bound payload in the same classification
chain. -/
abbrev reducedVolumePositiveLowerBoundPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (source : SingularityModelClassificationPayloadSource flow) :=
  source.asymptoticSolitonSource.nonnegativeCurvatureOperatorSource.structureTheorySource.curvatureNormalizationSource.pointedRescalingSource.limitExtractionSource.hamiltonCompactnessSource.collapsedBallBlowupSource.noLocalCollapsingContradictionSetupSource.kappaNoncollapsingFromReducedVolumeSource.reducedVolumeNonincreasingSource.reducedVolumeLimitRigiditySource.reducedVolumePositiveLowerBoundSource.payload

end SingularityModelClassificationPayloadSource

/-- A positive Ricci-norm threshold together with an exact assignment from its
high-curvature spacetime points to the pointed rescalings classified by one
actual singularity-model source. -/
structure PerelmanSingularityControlSpacetimeSource
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (classificationSource : SingularityModelClassificationPayloadSource flow) :
    Type (u + 1) where
  /-- Ricci-norm threshold defining the high-curvature spacetime points. -/
  highCurvatureThreshold : ℝ
  /-- The selected threshold is strictly positive. -/
  highCurvatureThresholdPositive : 0 < highCurvatureThreshold
  /-- Singularity model assigned to every high-curvature spacetime point. -/
  highCurvatureToSingularityModel :
    PerelmanHighRicciCurvatureSpacetimePoint flow highCurvatureThreshold →
      classificationSource.payload.singularityModelFamily
  /-- The assigned pointed rescaling occurs at the original spacetime time. -/
  pointedRescalingTime_eq :
    ∀ p,
      classificationSource.pointedRescalingPayload.pointedRescalingTime
          (classificationSource.singularityModelToPointedRescalingIndex
            (highCurvatureToSingularityModel p)) =
        p.1.1
  /-- The assigned pointed rescaling is based at the original spatial point. -/
  pointedRescalingBasepoint_eq :
    ∀ p,
      classificationSource.pointedRescalingPayload.pointedRescalingBasepoint
          (classificationSource.singularityModelToPointedRescalingIndex
            (highCurvatureToSingularityModel p)) =
        p.1.2
  /-- Every pointed rescaling comes from a genuine high-curvature spacetime point. -/
  pointedRescalingCoverage :
    Function.Surjective
      (fun p =>
        classificationSource.singularityModelToPointedRescalingIndex
          (highCurvatureToSingularityModel p))

namespace PerelmanSingularityControlSpacetimeSource

variable
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {classificationSource : SingularityModelClassificationPayloadSource flow}

/-- Coverage by high-curvature points implies the repaired classification
coverage of every pointed-rescaling index. -/
theorem singularityModelToPointedRescalingIndex_surjective
    (source :
      PerelmanSingularityControlSpacetimeSource flow classificationSource) :
    Function.Surjective
      classificationSource.singularityModelToPointedRescalingIndex := by
  intro index
  rcases source.pointedRescalingCoverage index with ⟨point, hpoint⟩
  exact ⟨source.highCurvatureToSingularityModel point, hpoint⟩

/-- The distinguished pointed-rescaling index has a genuine high-Ricci
spacetime preimage. -/
theorem highRicciCurvatureSpacetimePoint_nonempty
    (source :
      PerelmanSingularityControlSpacetimeSource flow classificationSource) :
    Nonempty
      (PerelmanHighRicciCurvatureSpacetimePoint flow
        source.highCurvatureThreshold) := by
  rcases source.pointedRescalingCoverage
      classificationSource.pointedRescalingPayload.basePointedRescalingIndex with
    ⟨point, _hpoint⟩
  exact ⟨point⟩

/-- The source supplies the repaired package-backed blow-up classification. -/
def toSingularityModelBlowupClassification
    (source :
      PerelmanSingularityControlSpacetimeSource flow classificationSource) :
    HasSingularityModelBlowupClassification flow :=
  HasSingularityModelBlowupClassification.of_classification_payload_source
    classificationSource
    source.singularityModelToPointedRescalingIndex_surjective

end PerelmanSingularityControlSpacetimeSource

/-- Production data tying high-curvature spacetime coverage, singularity
classification, reduced-volume monotonicity, and no-local-collapsing to the
same payload chain. -/
structure PerelmanSingularityControlProductionSource
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Type (u + 1) where
  /-- The actual singularity-model classification chain. -/
  classificationSource : SingularityModelClassificationPayloadSource flow
  /-- Reduced-volume monotonicity built on the chain's nonincreasing payload. -/
  reducedVolumeMonotonicityPayload :
    PerelmanReducedVolumeMonotonicityPayload
      classificationSource.reducedVolumeNonincreasingPayload
  /-- No-local-collapsing built on the chain's contradiction-setup payload. -/
  noLocalCollapsingPayload :
    PerelmanNoLocalCollapsingPayload
      classificationSource.noLocalCollapsingContradictionSetupPayload
  /-- Spacetime coverage of every pointed rescaling in the same chain. -/
  spacetime :
    PerelmanSingularityControlSpacetimeSource flow classificationSource

namespace PerelmanSingularityControlProductionSource

variable
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}

/-- The spatial projection of the genuine high-Ricci spacetime locus. -/
def highCurvatureRegion
    (source : PerelmanSingularityControlProductionSource flow) : Set M :=
  {x | ∃ t,
    source.spacetime.highCurvatureThreshold ≤
      perelmanRicciTensorNormAt flow t x}

/-- The basepoint range of the pointed rescalings in the classification chain. -/
def blowupModelRegion
    (source : PerelmanSingularityControlProductionSource flow) : Set M :=
  Set.range source.classificationSource.pointedRescalingPayload.pointedRescalingBasepoint

/-- The spatial high-curvature region is nonempty because every pointed
rescaling, including the distinguished one, has a high-Ricci spacetime preimage. -/
theorem highCurvatureRegion_nonempty
    (source : PerelmanSingularityControlProductionSource flow) :
    source.highCurvatureRegion.Nonempty := by
  rcases source.spacetime.highRicciCurvatureSpacetimePoint_nonempty with
    ⟨point⟩
  exact ⟨point.1.2, point.1.1, point.2⟩

/-- The high-curvature spatial projection is covered by actual pointed
rescaling basepoints. -/
theorem highCurvatureRegion_subset_blowupModelRegion
    (source : PerelmanSingularityControlProductionSource flow) :
    source.highCurvatureRegion ⊆ source.blowupModelRegion := by
  intro x hx
  rcases hx with ⟨t, htx⟩
  let point : PerelmanHighRicciCurvatureSpacetimePoint flow
      source.spacetime.highCurvatureThreshold :=
    ⟨(t, x), htx⟩
  refine ⟨source.classificationSource.singularityModelToPointedRescalingIndex
      (source.spacetime.highCurvatureToSingularityModel point), ?_⟩
  exact source.spacetime.pointedRescalingBasepoint_eq point

/-- The actual no-local-collapsing payload supplies its public interface. -/
def toPerelmanNoLocalCollapsing
    (source : PerelmanSingularityControlProductionSource flow) :
    HasPerelmanNoLocalCollapsing flow :=
  HasPerelmanNoLocalCollapsing.of_no_local_collapsing_payload
    source.noLocalCollapsingPayload

/-- The actual reduced-volume payload supplies its public interface. -/
def toPerelmanReducedVolumeMonotonicity
    (source : PerelmanSingularityControlProductionSource flow) :
    HasPerelmanReducedVolumeMonotonicity flow :=
  HasPerelmanReducedVolumeMonotonicity.of_reduced_volume_monotonicity_payload
    source.reducedVolumeMonotonicityPayload

/-- The canonical-neighborhood payload retained by the classification chain
supplies its public interface. -/
def toCanonicalNeighborhoodTheorem
    (source : PerelmanSingularityControlProductionSource flow) :
    HasCanonicalNeighborhoodTheorem flow :=
  HasCanonicalNeighborhoodTheorem.of_canonical_neighborhood_theorem_payload
    source.classificationSource.canonicalNeighborhoodTheoremPayload

/-- The retained classification source supplies its public interface. -/
def toSingularityModelClassification
    (source : PerelmanSingularityControlProductionSource flow) :
    HasSingularityModelClassification flow :=
  ⟨⟨source.classificationSource⟩⟩

/-- The spacetime coverage supplies the repaired blow-up-classification
interface on the same source. -/
def toSingularityModelBlowupClassification
    (source : PerelmanSingularityControlProductionSource flow) :
    HasSingularityModelBlowupClassification flow :=
  source.spacetime.toSingularityModelBlowupClassification

/-- The grounded production source determines an honest legacy aggregate
payload. Its three intermediate regions are the high-Ricci spatial projection,
and its blow-up region is exactly the pointed-rescaling basepoint range. -/
def toPerelmanSingularityControlPayload
    (source : PerelmanSingularityControlProductionSource flow) :
    PerelmanSingularityControlPayload flow
      source.toPerelmanNoLocalCollapsing
      source.toPerelmanReducedVolumeMonotonicity
      source.toCanonicalNeighborhoodTheorem
      source.toSingularityModelClassification
      source.toSingularityModelBlowupClassification where
  singularityControlScale :=
    source.classificationSource.canonicalNeighborhoodTheoremPayload.canonicalNeighborhoodTheoremScale
  singularityControlScalePositive :=
    source.classificationSource.canonicalNeighborhoodTheoremPayload.canonicalNeighborhoodTheoremScalePositive
  reducedVolumeLowerBound :=
    source.classificationSource.reducedVolumePositiveLowerBoundPayload.reducedVolumeLowerBoundConstant
  reducedVolumeLowerBoundPositive :=
    source.classificationSource.reducedVolumePositiveLowerBoundPayload.reducedVolumeLowerBoundConstantPositive
  kappaNoncollapsingScale := source.noLocalCollapsingPayload.noLocalCollapsingScale
  kappaNoncollapsingScalePositive :=
    source.noLocalCollapsingPayload.noLocalCollapsingScalePositive
  canonicalNeighborhoodScale :=
    source.classificationSource.canonicalNeighborhoodTheoremPayload.canonicalNeighborhoodTheoremScale
  canonicalNeighborhoodScalePositive :=
    source.classificationSource.canonicalNeighborhoodTheoremPayload.canonicalNeighborhoodTheoremScalePositive
  highCurvatureRegion := source.highCurvatureRegion
  canonicalNeighborhoodRegion := source.highCurvatureRegion
  highCurvatureRegion_subset_canonicalNeighborhoodRegion := by
    intro x hx
    exact hx
  singularityModelRegion := source.highCurvatureRegion
  canonicalNeighborhoodRegion_subset_singularityModelRegion := by
    intro x hx
    exact hx
  blowupModelRegion := source.blowupModelRegion
  singularityModelRegion_subset_blowupModelRegion := by
    exact source.highCurvatureRegion_subset_blowupModelRegion
  singularityControlDefect :=
    source.classificationSource.payload.singularityModelClassificationEnvelope
  singularityControlDefectNonnegative :=
    source.classificationSource.payload.singularityModelClassificationEnvelopeNonnegative
  singularityControlDefectBound :=
    source.classificationSource.payload.singularityModelClassificationEnvelope
  singularityControlDefectBoundNonnegative :=
    source.classificationSource.payload.singularityModelClassificationEnvelopeNonnegative
  singularityControlDefect_le_bound := le_rfl

@[simp]
theorem toPerelmanSingularityControlPayload_highCurvatureRegion
    (source : PerelmanSingularityControlProductionSource flow) :
    source.toPerelmanSingularityControlPayload.highCurvatureRegion =
      source.highCurvatureRegion :=
  rfl

@[simp]
theorem toPerelmanSingularityControlPayload_blowupModelRegion
    (source : PerelmanSingularityControlProductionSource flow) :
    source.toPerelmanSingularityControlPayload.blowupModelRegion =
      source.blowupModelRegion :=
  rfl

/-- In particular, the legacy payload produced from grounded data cannot use
an empty high-curvature region. -/
theorem toPerelmanSingularityControlPayload_highCurvatureRegion_nonempty
    (source : PerelmanSingularityControlProductionSource flow) :
    source.toPerelmanSingularityControlPayload.highCurvatureRegion.Nonempty := by
  rw [source.toPerelmanSingularityControlPayload_highCurvatureRegion]
  exact source.highCurvatureRegion_nonempty

/-- Project the grounded production source to the legacy public control
interface without losing the stronger source itself. -/
def toHasPerelmanSingularityControl
    (source : PerelmanSingularityControlProductionSource flow) :
    HasPerelmanSingularityControl flow :=
  HasPerelmanSingularityControl.of_perelman_singularity_control_payload
    source.toPerelmanSingularityControlPayload

/-- Assemble the full legacy Perelman package from the payloads retained in
the classification chain and this source's grounded aggregate inputs. -/
def toPerelmanSingularityControlPackage
    (source : PerelmanSingularityControlProductionSource flow) :
    PerelmanSingularityControlPackage flow := by
  let classificationSource := source.classificationSource
  let asymptoticSolitonSource := classificationSource.asymptoticSolitonSource
  let nonnegativeSource :=
    asymptoticSolitonSource.nonnegativeCurvatureOperatorSource
  let structureSource := nonnegativeSource.structureTheorySource
  let curvatureNormalizationSource :=
    structureSource.curvatureNormalizationSource
  let pointedSource := curvatureNormalizationSource.pointedRescalingSource
  let limitSource := pointedSource.limitExtractionSource
  let hamiltonSource := limitSource.hamiltonCompactnessSource
  let collapsedSource := hamiltonSource.collapsedBallBlowupSource
  let setupSource :=
    collapsedSource.noLocalCollapsingContradictionSetupSource
  let kappaSource := setupSource.kappaNoncollapsingFromReducedVolumeSource
  let nonincreasingSource := kappaSource.reducedVolumeNonincreasingSource
  let limitRigiditySource :=
    nonincreasingSource.reducedVolumeLimitRigiditySource
  let positiveLowerBoundSource :=
    limitRigiditySource.reducedVolumePositiveLowerBoundSource
  let rigiditySource := positiveLowerBoundSource.reducedVolumeRigiditySource
  let derivativeSource := rigiditySource.reducedVolumeDerivativeFormulaSource
  let definitionSource := derivativeSource.reducedVolumeDefinitionSource
  let distanceTheorySource := definitionSource.reducedDistanceTheorySource
  let jacobianSource := distanceTheorySource.reducedJacobianComparisonSource
  let cutLocusSource :=
    jacobianSource.reducedDistanceCutLocusControlSource
  let estimatesSource := cutLocusSource.reducedDistanceEstimatesSource
  let differentialSource :=
    estimatesSource.reducedDistanceDifferentialInequalitySource
  let existenceSource := differentialSource.reducedDistanceExistenceSource
  let firstVariationSource := existenceSource.reducedLengthFirstVariationSource
  exact
    perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_reduced_volume_monotonicity_payload_canonical_neighborhood_theorem_payload_singularity_model_classification_payload_and_components_and_control_payload
      firstVariationSource.fFunctionalPayload
      firstVariationSource.entropyNormalizationPayload
      firstVariationSource.entropyMinimizerPayload
      firstVariationSource.entropyLogSobolevPayload
      firstVariationSource.conjugateHeatPayload
      firstVariationSource.adjointHeatPayload
      firstVariationSource.conjugateHeatKernelEstimatesPayload
      firstVariationSource.wFunctionalPayload
      firstVariationSource.entropyGradientPayload
      firstVariationSource.entropyFirstVariationPayload
      firstVariationSource.entropyMonotonicityPayload
      firstVariationSource.entropyLowerBoundPropagationPayload
      firstVariationSource.entropyFunctionalPayload
      firstVariationSource.payload
      existenceSource.payload differentialSource.payload estimatesSource.payload
      cutLocusSource.payload jacobianSource.payload distanceTheorySource.payload
      definitionSource.payload derivativeSource.payload rigiditySource.payload
      positiveLowerBoundSource.payload limitRigiditySource.payload
      nonincreasingSource.payload source.reducedVolumeMonotonicityPayload
      kappaSource.payload setupSource.payload collapsedSource.payload
      hamiltonSource.payload classificationSource.ancientCompactnessPayload
      limitSource.payload pointedSource.payload
      curvatureNormalizationSource.payload structureSource.payload
      nonnegativeSource.payload asymptoticSolitonSource.payload
      classificationSource.scaleControlPayload
      classificationSource.stabilityPayload
      classificationSource.persistencePayload
      classificationSource.neckCapPayload
      classificationSource.classificationPayload
      classificationSource.canonicalNeighborhoodTheoremPayload
      classificationSource.payload source.noLocalCollapsingPayload
      source.toSingularityModelBlowupClassification
      source.toPerelmanSingularityControlPayload

end PerelmanSingularityControlProductionSource

/-- Grounded singularity control retains the nonempty production source, so
the public interface cannot be supplied through empty curvature regions. -/
structure GroundedPerelmanSingularityControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop where
  source : Nonempty (PerelmanSingularityControlProductionSource flow)

namespace GroundedPerelmanSingularityControl

variable
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}

/-- Package one grounded production source. -/
def ofSource
    (source : PerelmanSingularityControlProductionSource flow) :
    GroundedPerelmanSingularityControl flow :=
  ⟨⟨source⟩⟩

/-- Forgetting the retained source gives the legacy public control interface. -/
theorem toHasPerelmanSingularityControl
    (grounded : GroundedPerelmanSingularityControl flow) :
    HasPerelmanSingularityControl flow := by
  rcases grounded.source with ⟨source⟩
  exact source.toHasPerelmanSingularityControl

/-- Select the retained nonvacuous source and assemble its complete legacy
Perelman package. -/
noncomputable def toPerelmanSingularityControlPackage
    (grounded : GroundedPerelmanSingularityControl flow) :
    PerelmanSingularityControlPackage flow :=
  (Classical.choice grounded.source).toPerelmanSingularityControlPackage

/-- Grounded control contains a real high-Ricci spacetime point at a positive
threshold. -/
theorem exists_highRicciCurvatureSpacetimePoint
    (grounded : GroundedPerelmanSingularityControl flow) :
    ∃ source : PerelmanSingularityControlProductionSource flow,
      0 < source.spacetime.highCurvatureThreshold ∧
        Nonempty
          (PerelmanHighRicciCurvatureSpacetimePoint flow
            source.spacetime.highCurvatureThreshold) := by
  rcases grounded.source with ⟨source⟩
  exact
    ⟨source, source.spacetime.highCurvatureThresholdPositive,
      source.spacetime.highRicciCurvatureSpacetimePoint_nonempty⟩

end GroundedPerelmanSingularityControl

end Poincare
