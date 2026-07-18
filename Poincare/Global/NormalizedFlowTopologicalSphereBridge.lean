import Poincare.Global.SmoothabilityExistenceBridge
import Poincare.Global.SmoothabilityProofBearingAtlasUpgrade
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinScalarProfile

/-!
# Noncircular topological-to-normalized-flow sphere bridge

This module applies the strongest finite-time normalized-flow sphere endpoint
to one fixed target-layer compact simply connected topological
three-manifold.

The four boundaries remain separate and visible:

1. `AdmitsSurgeryModelSmoothStructure M` selects a surgery-model `C¹` atlas;
2. `C1ToCInfinityAtlasUpgrade3 M` is the sole smoothing upgrade premise;
3. `FixedTargetNormalizedFlowSphereAnalyticData3 M` supplies exactly the
   analytic inputs of the strongest smooth normalized-flow corollary; and
4. `UnitConstantCurvatureSphereRecognition3 M` performs only the final
   unit-curvature recognition step.

No one-point or three-sphere recognition theorem is used to construct the
smooth atlas.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

local notation "I" => closedSmoothModelWithCorners 3

/-- The exact analytic inputs of the strongest tensor-reference/range-only
normalized-flow sphere corollary on one already-smooth target.

This structure deliberately contains neither smoothability nor sphere
recognition data.  Its fields are precisely the compact reference family,
normalized flow, dissipation and regularity estimates, uniform scalar floor,
Hamilton quotient evolution, improved traceless-pinching evolution, and
integer-time invariant-range compactness consumed by
`sphereConclusion_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range`.
-/
structure NormalizedFlowSphereAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  nonemptyK : Nonempty K
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : ℝ → K
  realizesFlow : ∀ t, metric (parameter t) = gt t
  compactControl :
    letI : TopologicalSpace K := topologicalSpaceK
    CompactReferenceMetricTensorFamilyData K metric
  A : ℝ
  B : ℝ
  rho : ℝ
  covariantDerivativeRegularity : ∀ t : ℝ,
    CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1
  rho_pos : 0 < rho
  flow : ∀ t : ℝ, ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  differentiateMovingTotalScalar : ∀ t : ℝ,
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t
  differentiateMovingVolume : ∀ t : ℝ,
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t
  finiteDissipation :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)
  tracelessRicciEnergyCOne : UniformTracelessRicciEnergyCOne gt
  tracelessRicciBounds :
    UniformTracelessRicciAndCovariantDerivativeNormBound gt A B
  scalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
    rho ≤ (gt t).scalarAt x
  pinchingQuotientContinuous : ∀ t : ℝ, 0 ≤ t →
    Continuous ↿(fun s (x : M) ↦ (gt (t + s)).pinchingQuotientAt x)
  pinchingQuotientContMDiffTwo :
    ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x
  pinchingQuotientEvolution :
    ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x)
  tracelessPinchingContinuous : ∀ t : ℝ, 0 ≤ t →
    Continuous ↿(fun s (x : M) ↦
      (gt (t + s)).tracelessPinchingAt x 0)
  tracelessPinchingContMDiffTwo :
    ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x
  tracelessPinchingEvolution :
    ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x)
  invariantPairRangeCompact : ∀ t : ℝ, 0 ≤ t → IsCompact
    (Set.range fun i : ℕ ↦
      closedMetricScalarMinimumRelativePinchingMaximumPair
        (gt (t + (i : ℝ))))

/-- The fixed-target analytic provider is polymorphic only in the smooth
instances selected by the noncomputable atlas bridge.  The measurable
structure is fixed canonically to the Borel measurable space.  Every actual
geometric hypothesis remains a named field of
`NormalizedFlowSphereAnalyticData3`. -/
def FixedTargetNormalizedFlowSphereAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereAnalyticData3.{u, v} M

/-- Scalar-profile specialization of the fixed-target analytic data.

Compared with `NormalizedFlowSphereAnalyticData3`, the opaque numerical
`rho` and all-forward `scalarLower` fields are absent.  They are replaced by
pointwise positivity on the initial slice, Lichnerowicz regularity, joint
scalar continuity, and a normalization primitive whose forward increment is
bounded above.  The scalar-profile maximum-principle endpoint constructs the
uniform positive floor from these fields.
-/
structure NormalizedFlowSphereScalarProfileAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  nonemptyK : Nonempty K
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : ℝ → K
  realizesFlow : ∀ t, metric (parameter t) = gt t
  compactControl :
    letI : TopologicalSpace K := topologicalSpaceK
    CompactReferenceMetricTensorFamilyData K metric
  A : ℝ
  B : ℝ
  primitiveUpperBound : ℝ
  covariantDerivativeRegularity : ∀ t : ℝ,
    CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1
  flow : ∀ t : ℝ, ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  lichnerowicz : GlobalLichnerowiczAssemblyRegularity gt
  scalarContinuous :
    Continuous ↿(fun tau (x : M) ↦ (gt tau).scalarAt x)
  normalizationPrimitive : ℝ → ℝ
  normalizationPrimitiveContinuous : Continuous normalizationPrimitive
  normalizationPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
    HasDerivAt normalizationPrimitive
      ((2 / 3 : ℝ) * meanScalar (gt tau)) tau
  normalizationPrimitiveUpper : ∀ tau ∈ Ici (0 : ℝ),
    normalizationPrimitive tau - normalizationPrimitive 0 ≤
      primitiveUpperBound
  initialScalarPos : ∀ x : M, 0 < (gt 0).scalarAt x
  differentiateMovingTotalScalar : ∀ t : ℝ,
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t
  differentiateMovingVolume : ∀ t : ℝ,
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t
  finiteDissipation :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)
  tracelessRicciEnergyCOne : UniformTracelessRicciEnergyCOne gt
  tracelessRicciBounds :
    UniformTracelessRicciAndCovariantDerivativeNormBound gt A B
  pinchingQuotientContinuous : ∀ t : ℝ, 0 ≤ t →
    Continuous ↿(fun s (x : M) ↦ (gt (t + s)).pinchingQuotientAt x)
  pinchingQuotientContMDiffTwo :
    ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x
  pinchingQuotientEvolution :
    ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x)
  tracelessPinchingContinuous : ∀ t : ℝ, 0 ≤ t →
    Continuous ↿(fun s (x : M) ↦
      (gt (t + s)).tracelessPinchingAt x 0)
  tracelessPinchingContMDiffTwo :
    ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x
  tracelessPinchingEvolution :
    ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x)
  invariantPairRangeCompact : ∀ t : ℝ, 0 ≤ t → IsCompact
    (Set.range fun i : ℕ ↦
      closedMetricScalarMinimumRelativePinchingMaximumPair
        (gt (t + (i : ℝ))))

/-- Fixed-target provider for the scalar-profile analytic package, with the
canonical Borel measurable structure installed under the selected smooth
atlas. -/
def FixedTargetNormalizedFlowSphereScalarProfileAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereScalarProfileAnalyticData3.{u, v} M

/-- The scalar-profile package reaches the strongest smooth sphere endpoint,
deriving its uniform positive scalar floor rather than storing one. -/
theorem NormalizedFlowSphereScalarProfileAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : NormalizedFlowSphereScalarProfileAnalyticData3.{u, v} M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  letI : Nonempty data.K := data.nonemptyK
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1 :=
    data.covariantDerivativeRegularity
  exact
    sphereConclusion_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
      data.gt data.metric data.parameter data.realizesFlow data.compactControl
      data.flow data.lichnerowicz data.scalarContinuous
      data.normalizationPrimitive data.normalizationPrimitiveContinuous
      data.normalizationPrimitiveDerivative data.normalizationPrimitiveUpper
      data.initialScalarPos data.differentiateMovingTotalScalar
      data.differentiateMovingVolume data.finiteDissipation
      data.tracelessRicciEnergyCOne data.tracelessRicciBounds
      data.pinchingQuotientContinuous data.pinchingQuotientContMDiffTwo
      data.pinchingQuotientEvolution data.tracelessPinchingContinuous
      data.tracelessPinchingContMDiffTwo data.tracelessPinchingEvolution
      data.invariantPairRangeCompact unitRecognition

/-- The analytic package reaches the strongest smooth sphere corollary while
leaving unit-curvature recognition as an explicit final premise. -/
theorem NormalizedFlowSphereAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : NormalizedFlowSphereAnalyticData3.{u, v} M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  letI : Nonempty data.K := data.nonemptyK
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1 :=
    data.covariantDerivativeRegularity
  exact
    sphereConclusion_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
      data.gt data.metric data.parameter data.realizesFlow data.compactControl
      data.rho_pos data.flow data.differentiateMovingTotalScalar
      data.differentiateMovingVolume data.finiteDissipation
      data.tracelessRicciEnergyCOne data.tracelessRicciBounds
      data.scalarLower data.pinchingQuotientContinuous
      data.pinchingQuotientContMDiffTwo data.pinchingQuotientEvolution
      data.tracelessPinchingContinuous data.tracelessPinchingContMDiffTwo
      data.tracelessPinchingEvolution data.invariantPairRangeCompact
      unitRecognition

/-- Noncircular fixed-target sphere conclusion.

`AdmitsSurgeryModelSmoothStructure` and `C1ToCInfinityAtlasUpgrade3` are used
only to install the smooth normalized-flow instances.  The analytic provider
then constructs a unit-curvature metric, and the separately quantified
`UnitConstantCurvatureSphereRecognition3` provider recognizes that metric.
None of these four boundaries is inferred from another. -/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_upgrade_of_normalizedFlowAnalyticData_of_unitRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (upgrade : C1ToCInfinityAtlasUpgrade3 M)
    (analytic : FixedTargetNormalizedFlowSphereAnalyticData3.{u, v} M)
    (unitRecognition :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  refine normalizedFlowTarget_elim_of_admitsSurgeryModelSmoothStructure
    admits upgrade ?_
  intro _charted _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact analytic.sphereConclusion unitRecognition

/-- Strongest noncircular fixed-target sphere conclusion with the scalar
floor generated from initial positivity and a bounded normalization
primitive.

The theorem does not assume an all-forward `rho` or `scalarLower`.  It still
keeps the selected `C¹` smooth structure, its independent `C∞` upgrade,
integer-time invariant-pair compactness inside the analytic package, and the
final unit-curvature recognition provider as separate boundaries. -/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_upgrade_of_normalizedFlowScalarProfileAnalyticData_of_unitRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (upgrade : C1ToCInfinityAtlasUpgrade3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereScalarProfileAnalyticData3.{u, v} M)
    (unitRecognition :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  refine normalizedFlowTarget_elim_of_admitsSurgeryModelSmoothStructure
    admits upgrade ?_
  intro _charted _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact analytic.sphereConclusion unitRecognition

/-- End-to-end noncircular target theorem with the smoothing boundary reduced
to local `C∞` transition compatibility.

The local smoothing provider selects an atlas and proves precisely the
transition condition consumed by `isManifold_of_contDiffOn`; the pointwise
`C1ToCInfinityAtlasUpgrade3` premise is therefore a conclusion rather than an
argument.  The Moise-shaped `C¹` existence, scalar-profile analytic package
(including integer-time invariant-pair compactness), and unit-curvature
recognition remain independent explicit inputs. -/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_localTransitionSmoothing_of_normalizedFlowScalarProfileAnalyticData_of_unitRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereScalarProfileAnalyticData3.{u, v} M)
    (unitRecognition :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_upgrade_of_normalizedFlowScalarProfileAnalyticData_of_unitRecognition
    admits
    (c1ToCInfinityAtlasUpgrade3_of_localTransitionSmoothing localSmoothing)
    analytic unitRecognition

end Poincare
