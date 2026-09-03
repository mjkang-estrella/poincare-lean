import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffPositiveEinstein
import Poincare.Global.MetricFlowJointCovRicciNormContinuity

/-!
# Compact joint covariant-Ricci control for the Hausdorff reaction endpoint

The Hausdorff reaction-decay endpoint previously stored both a real number
`D` and a proof that `|∇ Ric|² ≤ D²` on every nonnegative flow slice.  For a
flow realized inside a compact metric family, that pair is produced by one
geometric continuity statement: joint continuity of the squared intrinsic
covariant-Ricci norm on `K × M`.

This module proves the compact maximum argument and uses it to remove the
chosen bound and its verification from the analytic input package.  The
compact tensor-reference comparison remains explicit; constructing that
comparison from a topology on the space of metrics is a separate issue.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/-- Joint continuity of the squared full covariant-Ricci norm on a compact
metric family supplies one positive uniform intrinsic bound.

The maximum itself is nonnegative.  Enlarging it by one gives a strictly
positive number which is at most its own square and whose square therefore
dominates every value in the family. -/
theorem exists_pos_uniform_covRicciNormSqAt_bound_of_compact_joint
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hJoint : Continuous ↿(fun k (x : M) ↦
      covRicciNormSqAt (metric k) x)) :
    ∃ D : ℝ, 0 < D ∧ ∀ k : K, ∀ x : M,
      covRicciNormSqAt (metric k) x ≤ D ^ 2 := by
  obtain ⟨pMax, _hpMax, hpMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (K × M))).exists_isMaxOn
      Set.univ_nonempty hJoint.continuousOn
  let S : ℝ := covRicciNormSqAt (metric pMax.1) pMax.2
  have hSNonneg : 0 ≤ S := by
    dsimp only [S]
    exact covRicciNormSqAt_nonneg (g := metric pMax.1) pMax.2
  let D : ℝ := S + 1
  have hDpos : 0 < D := by
    dsimp only [D]
    exact add_pos_of_nonneg_of_pos hSNonneg zero_lt_one
  have hOneLeD : (1 : ℝ) ≤ D := by
    dsimp only [D]
    calc
      (1 : ℝ) = 1 + 0 := (add_zero 1).symm
      _ ≤ 1 + S := add_le_add_right hSNonneg 1
      _ = S + 1 := add_comm 1 S
  have hDleSq : D ≤ D ^ 2 := by
    calc
      D = D * 1 := (mul_one D).symm
      _ ≤ D * D := mul_le_mul_of_nonneg_left hOneLeD hDpos.le
      _ = D ^ 2 := (pow_two D).symm
  have hSleSq : S ≤ D ^ 2 :=
    (le_add_of_nonneg_right zero_le_one : S ≤ S + 1).trans hDleSq
  refine ⟨D, hDpos, ?_⟩
  intro k x
  have hle : covRicciNormSqAt (metric k) x ≤ S := by
    simpa only [S] using hpMax (Set.mem_univ (k, x))
  exact hle.trans hSleSq

/-- Global joint `C³` metric-entry regularity supplies a uniform intrinsic
covariant-Ricci derivative bound on every nonempty compact time slab. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_on_compact_slab_of_metricEntriesJointContDiffAt_three
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {a b : ℝ} (hab : a ≤ b)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    ∃ D : ℝ,
      UniformCovariantRicciDerivativeNormBound
        (fun t : Set.Icc a b ↦ gt t.1) D := by
  letI : Nonempty (Set.Icc a b) := ⟨⟨a, left_mem_Icc.mpr hab⟩⟩
  have hInclude : Continuous
      (fun p : Set.Icc a b × M ↦ ((p.1.1 : ℝ), p.2)) :=
    continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd
  have hJointReal : Continuous
      (fun p : ℝ × M ↦ covRicciNormSqAt (gt p.1) p.2) :=
    continuous_covRicciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
      (n := 3) (M := M) hJoint
  have hJointSlab : Continuous
      (fun p : Set.Icc a b × M ↦
        covRicciNormSqAt (gt p.1.1) p.2) := by
    change Continuous
      ((fun p : ℝ × M ↦ covRicciNormSqAt (gt p.1) p.2) ∘
        (fun p : Set.Icc a b × M ↦ ((p.1.1 : ℝ), p.2)))
    exact hJointReal.comp hInclude
  exact
    exists_pos_uniform_covRicciNormSqAt_bound_of_compact_joint
      (fun t : Set.Icc a b ↦ gt t.1) hJointSlab

/-- Hausdorff reaction-decay positive-Einstein data in which full
covariant-Ricci derivative control is represented by joint continuity on the
already stored compact metric family. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3
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
  scalarDomination :
    GlobalFiniteHausdorffChartFrameScalarDomination
      reaction.compactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation
  scalarStokes : ∀ t : Ici (0 : ℝ),
    ClosedLaplacianStokes (reaction.gt t.1)
      (fun y ↦ (reaction.gt t.1).scalarAt y)

/-- Fixed-target form of the joint-covariant-Ricci Hausdorff package. -/
def FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3

variable [SimplyConnectedSpace M]

/-- Compactness constructs the omitted derivative bound and recovers the
verified Hausdorff reaction-decay positive-Einstein package. -/
noncomputable def toHausdorffPositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
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
  exact {
    reaction := reaction
    compactTensorReferenceControl := data.compactTensorReferenceControl
    fullCovariantRicciDerivativeBound := D
    fullCovariantRicciControl := ⟨hD, fun t x ↦ by
      change covRicciNormSqAt (reaction.gt t.1) x ≤ D ^ 2
      rw [← reaction.realizesFlow t]
      exact hCov (reaction.parameter t) x⟩
    scalarDomination := data.scalarDomination
    scalarStokes := data.scalarStokes }

/-- The compact joint-covariant-Ricci package constructs finite forward
traceless-Ricci energy. -/
theorem finiteTracelessRicciEnergy
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack data.reaction.gt) (Ici 0) :=
  data.toHausdorffPositiveEinsteinAnalyticData3.finiteTracelessRicciEnergy

/-- The same package constructs finite absolute normalized-flow
dissipation. -/
theorem finiteAbsoluteDissipation
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedMeanScalarAbsoluteVarianceDissipation data.reaction.gt)
      (Ici 0) :=
  data.toHausdorffPositiveEinsteinAnalyticData3.finiteAbsoluteDissipation

/-- Joint compact curvature control reaches the positive Einstein endpoint. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M :=
  data.toHausdorffPositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- The positive Einstein metric has a unit-curvature normalization. -/
theorem existsUnitConstantCurvature
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 :=
  data.toHausdorffPositiveEinsteinAnalyticData3.existsUnitConstantCurvature

/-- Unit-curvature recognition supplies the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toHausdorffPositiveEinsteinAnalyticData3.sphereConclusion unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3

/-- Pointwise conversion of the fixed-target joint-continuity package. -/
noncomputable def
    fixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3_of_jointCovRicci
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
        M) :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
      M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact data.toHausdorffPositiveEinsteinAnalyticData3

end Poincare
