import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinstein
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction

/-!
# Compact reaction endpoint from joint scalar-derivative regularity

This module removes the remaining chartwise scalar-domination record from
the compact Hausdorff reaction endpoint.  The replacement is intrinsic joint
continuity of the actual scalar-curvature time derivative.  Together with
the reaction package's joint `C³` metric entries, the compact finite atlas,
and the finite subordinate Laplacian geometry, the local restriction theorem
constructs the moving total-scalar derivative.

Compactness still constructs the uniform full covariant-Ricci derivative
bound.  Thus neither a scalar-density domination package nor a Stokes
conclusion is retained as a field.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/-- Joint covariant-Ricci norm continuity from the scalar Bochner fields. -/
theorem continuous_joint_covRicciNormSqAt_of_bochner_fields {n : ℕ} {N : Type u} {K : Type v} [TopologicalSpace N] [T2Space N] [ChartedSpace (ClosedSmoothModel n) N] [IsManifold (closedSmoothModelWithCorners n) ∞ N] [TopologicalSpace K] (metric : K → ClosedSmoothRiemannianMetric n N) (hRicNorm₂ : ∀ k : K, ∀ x : N, ContMDiffAt (closedSmoothModelWithCorners n) 𝓘(ℝ) 2 (fun y : N ↦ (metric k).ricciNormSqAt y) x) (hPairDiff : ∀ k : K, ∀ x : N, ∀ w : TangentSpace (closedSmoothModelWithCorners n) x, MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (fun y : N ↦ covRicciRicciPairingAt (metric k) y (extend (ClosedSmoothModel n) w y)) x) (hRicSecond : ∀ k : K, ∀ x : N, CovTensor2DerivExtDifferentiableAt (metric k) (ricciVariationField (metric k)) x) (hLaplacian : Continuous (fun p : K × N ↦ (metric p.1).laplacianAt (fun y : N ↦ (metric p.1).ricciNormSqAt y) p.2)) (hRough : Continuous (fun p : K × N ↦ roughRicciLaplacianPairingAt (metric p.1) p.2)) : Continuous (fun p : K × N ↦ covRicciNormSqAt (metric p.1) p.2) := by
  have hformula : (fun p : K × N ↦ covRicciNormSqAt (metric p.1) p.2) = fun p : K × N ↦ ((metric p.1).laplacianAt (fun y : N ↦ (metric p.1).ricciNormSqAt y) p.2 - 2 * roughRicciLaplacianPairingAt (metric p.1) p.2) / 2 := by
    funext p
    have hBochner := laplacianAt_ricciNormSqAt_eq_two_roughPairing_add_two_covNormSq (metric p.1) p.2 (hRicNorm₂ p.1 p.2) (hPairDiff p.1 p.2) (hRicSecond p.1 p.2)
    linarith
  rw [hformula]
  exact (hLaplacian.sub (hRough.const_mul 2)).div_const 2

/-- The C2 Ricci-norm premise also supplies the Bochner pairing differentiability premise. -/
theorem continuous_joint_covRicciNormSqAt_of_bochner_norm_fields
    {n : ℕ} {N : Type u} {K : Type v}
    [TopologicalSpace N] [T2Space N]
    [ChartedSpace (ClosedSmoothModel n) N]
    [IsManifold (closedSmoothModelWithCorners n) ∞ N]
    [TopologicalSpace K]
    (metric : K → ClosedSmoothRiemannianMetric n N)
    (hRicNorm₂ : ∀ k : K, ∀ x : N,
      ContMDiffAt (closedSmoothModelWithCorners n)
        (modelWithCornersSelf ℝ ℝ) 2
        (fun y : N ↦ (metric k).ricciNormSqAt y) x)
    (hRicSecond : ∀ k : K, ∀ x : N,
      CovTensor2DerivExtDifferentiableAt (metric k)
        (ricciVariationField (metric k)) x)
    (hLaplacian : Continuous (fun p : K × N ↦
      (metric p.1).laplacianAt
        (fun y : N ↦ (metric p.1).ricciNormSqAt y) p.2))
    (hRough : Continuous (fun p : K × N ↦
      roughRicciLaplacianPairingAt (metric p.1) p.2)) :
    Continuous (fun p : K × N ↦
      covRicciNormSqAt (metric p.1) p.2) := by
  exact continuous_joint_covRicciNormSqAt_of_bochner_fields
    metric hRicNorm₂
    (fun k x w =>
      covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
        (metric k) x (hRicNorm₂ k x) w)
    hRicSecond hLaplacian hRough

/-- Reaction-decay data with scalar-density domination lowered to intrinsic
joint continuity of the scalar time derivative and Stokes lowered to finite
subordinate coordinate geometry. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  reaction :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
      M
  compactTensorReferenceControl :
    letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
    CompactReferenceMetricTensorFamilyData reaction.K reaction.metric
  covariantRicciNormSqJointContinuous :
    letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
    Continuous (fun p : reaction.K × M ↦
      covRicciNormSqAt (reaction.metric p.1) p.2)
  scalarTimeDerivativeJointContinuous :
    ScalarTimeDerivativeJointContinuous reaction.gt
  scalarSubordinateGeometry : ∀ t : Ici (0 : ℝ),
    FiniteSubordinateHausdorffLaplacianGeometry
      (reaction.gt t.1) (fun y ↦ (reaction.gt t.1).scalarAt y)

/-- Fixed-target form of the fully lowered Hausdorff analytic package. -/
def FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3

variable [SimplyConnectedSpace M]

/-- Construct from reaction fields, deriving scalar-time-derivative continuity automatically. -/
noncomputable def ofReactionFields
    (reaction : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M)
    (compactTensorReferenceControl : letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      Poincare.CompactReferenceMetricTensorFamilyData reaction.K reaction.metric)
    (covariantRicciNormSqJointContinuous : letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      Continuous (fun p : reaction.K × M ↦ Poincare.covRicciNormSqAt (reaction.metric p.1) p.2))
    (scalarSubordinateGeometry : (t : Set.Ici (0 : ℝ)) → Poincare.FiniteSubordinateHausdorffLaplacianGeometry
      (reaction.gt t.1) (fun y ↦ (reaction.gt t.1).scalarAt y)) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v} M :=
  { reaction := reaction
    compactTensorReferenceControl := compactTensorReferenceControl
    covariantRicciNormSqJointContinuous := covariantRicciNormSqJointContinuous
    scalarTimeDerivativeJointContinuous :=
      scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three
        reaction.jointMetricEntries
    scalarSubordinateGeometry := scalarSubordinateGeometry }

  /-- Construct from Bochner scalar fields, deriving joint covariant-Ricci continuity automatically. -/
  noncomputable def ofBochnerFields
    (reaction : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M)
    (compactTensorReferenceControl : letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      Poincare.CompactReferenceMetricTensorFamilyData reaction.K reaction.metric)
    (hRicNorm₂ : ∀ k : reaction.K, ∀ x : M, ContMDiffAt (Poincare.closedSmoothModelWithCorners 3)
      (modelWithCornersSelf ℝ ℝ) 2 (fun y : M ↦ (reaction.metric k).ricciNormSqAt y) x)
    (hPairDiff : ∀ k : reaction.K, ∀ x : M, ∀ w : TangentSpace (Poincare.closedSmoothModelWithCorners 3) x,
      MDifferentiableAt (Poincare.closedSmoothModelWithCorners 3) (modelWithCornersSelf ℝ ℝ)
      (fun y : M ↦ Poincare.covRicciRicciPairingAt (reaction.metric k) y
        (FiberBundle.extend (Poincare.ClosedSmoothModel 3) w y)) x)
    (hRicSecond : ∀ k : reaction.K, ∀ x : M,
      Poincare.CovTensor2DerivExtDifferentiableAt (reaction.metric k)
        (Poincare.ricciVariationField (reaction.metric k)) x)
    (hLaplacianJointContinuous : letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      Continuous (fun p : reaction.K × M ↦
        (reaction.metric p.1).laplacianAt (fun y : M ↦ (reaction.metric p.1).ricciNormSqAt y) p.2))
    (hRoughJointContinuous : letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      Continuous (fun p : reaction.K × M ↦
        Poincare.roughRicciLaplacianPairingAt (reaction.metric p.1) p.2))
    (scalarSubordinateGeometry : (t : Set.Ici (0 : ℝ)) → Poincare.FiniteSubordinateHausdorffLaplacianGeometry
      (reaction.gt t.1) (fun y ↦ (reaction.gt t.1).scalarAt y)) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v} M :=
  letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
  ofReactionFields reaction compactTensorReferenceControl
    (continuous_joint_covRicciNormSqAt_of_bochner_fields reaction.metric hRicNorm₂ hPairDiff hRicSecond
      hLaplacianJointContinuous hRoughJointContinuous)
    scalarSubordinateGeometry

/-- Local finite-atlas domination constructs the moving total-scalar
identity, finite subordinate geometry constructs Stokes, and compactness
constructs the omitted uniform covariant-Ricci bound. -/
noncomputable def toReactionDecayPositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
      M := by
  let reaction := data.reaction
  letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
  letI : CompactSpace reaction.K := reaction.compactSpaceK
  letI : Nonempty reaction.K :=
    ⟨reaction.parameter ⟨0, by simp⟩⟩
  let hexists :=
    exists_pos_uniform_covRicciNormSqAt_bound_of_compact_joint
      reaction.metric data.covariantRicciNormSqJointContinuous
  let D : ℝ := Classical.choose hexists
  have hD : 0 < D := (Classical.choose_spec hexists).1
  have hCov : ∀ k : reaction.K, ∀ x : M,
      covRicciNormSqAt (reaction.metric k) x ≤ D ^ 2 :=
    (Classical.choose_spec hexists).2
  let fullCovariantRicciControl :
      UniformCovariantRicciDerivativeNormBound
        (fun t : Ici (0 : ℝ) ↦ reaction.gt t.1) D :=
    ⟨hD, fun t x ↦ by
      change covRicciNormSqAt (reaction.gt t.1) x ≤ D ^ 2
      rw [← reaction.realizesFlow t]
      exact hCov (reaction.parameter t) x⟩
  letI : ∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (reaction.gt s).leviCivita 1 :=
    fun _s ↦ inferInstance
  let lichnerowicz : GlobalLichnerowiczAssemblyRegularity reaction.gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
      reaction.jointMetricEntries
  exact {
    reaction := reaction
    compactTensorReferenceControl := data.compactTensorReferenceControl
    fullCovariantRicciDerivativeBound := D
    fullCovariantRicciControl := fullCovariantRicciControl
    differentiateMovingTotalScalar := fun t ↦
      hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
        reaction.compactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation
        reaction.jointMetricEntries data.scalarTimeDerivativeJointContinuous
        lichnerowicz t.1 (reaction.normalizedFlow t.1 t.2)
        (data.scalarSubordinateGeometry t).closedLaplacianStokes }

/-- The fully lowered analytic package constructs finite forward
traceless-Ricci energy. -/
theorem finiteTracelessRicciEnergy
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack data.reaction.gt) (Ici 0) :=
  data.toReactionDecayPositiveEinsteinAnalyticData3.finiteTracelessRicciEnergy

/-- The same package reaches the positive Einstein endpoint. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M :=
  data.toReactionDecayPositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- Unit-curvature recognition supplies the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toReactionDecayPositiveEinsteinAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3

/-- Fixed-target conversion into the established reaction-decay positive-
Einstein endpoint. -/
noncomputable def
    fixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3_of_jointScalarDerivativeCovRicciSubordinatePartition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    FixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3.{u, v}
      M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact data.toReactionDecayPositiveEinsteinAnalyticData3

end Poincare
