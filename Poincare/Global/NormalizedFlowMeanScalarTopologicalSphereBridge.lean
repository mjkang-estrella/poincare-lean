import Poincare.Global.SmoothabilityExistenceBridge
import Poincare.Global.SmoothabilityProofBearingAtlasUpgrade
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination

/-!
# Fixed-target topological sphere bridge for the mean-scalar route

This module keeps the analytic and recognition boundaries separate from the
selected smooth-transition atlas needed to run them:

1. `CInfinityLocalTransitionAtlasData3 M` supplies one selected atlas and its
   `C∞` transition-map proof;
2. the mean-scalar analytic provider supplies the direct-sample normalized
   flow data under that selected smooth atlas; and
3. `UnitConstantCurvatureSphereRecognition3 M` performs only the final
   recognition of the constructed unit-curvature metric.

For compatibility with the Moise-shaped split boundary, a corollary still
accepts `AdmitsSurgeryModelSmoothStructure M` together with
`C1AtlasLocalTransitionSmoothing3 M` and specializes the latter at the
admitted `C¹` atlas.

The analytic package contains no negative-time geometric hypotheses, Hamilton
evolution or antitonicity fields,
no scalar-variance Lipschitz field, no pointwise scalar floor, no
normalization primitive, no forward scalar-positivity field, and no pinching
quotient.  It also contains no opaque finite-absolute-dissipation field:
the geometric scalar-variance/traceless-energy domination inequality and
finite time-integrated traceless-Ricci energy reduce to that conclusion inside
the consumer.  The exact three-dimensional mean-scalar evolution identity
derives derivative nonnegativity from the domination inequality rather than
storing it as an independent analytic sign premise.  Its
compact-family invariant-pair continuity, uniform scalar bound, and uniform
traceless-Ricci norm bound are derived from joint scalar/traceless-Ricci
continuity on `K × M`, rather than stored as opaque fields.  No recognition
theorem is used to choose the smooth atlas.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- Exact forward full-covariant-Ricci analytic data for the direct-sample
mean-scalar sphere endpoint on an already smooth closed `3`-manifold.

Joint `C³` metric-entry regularity constructs the spatial regularity needed
by the scalar- and traceless-energy Lipschitz bridges.  The final two fields
are concrete compact-family product-space continuity hypotheses: together
they construct both the denominator-free invariant-pair continuity and the
uniform pointwise traceless-Ricci norm bound inside the downstream endpoint.
The ambient path `gt` remains real-indexed only because differentiation and
time integrals are stated on real time; every geometric datum is indexed by
the proof-carrying forward subtype `Ici 0`. -/
structure NormalizedFlowSphereMeanScalarAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : Ici (0 : ℝ) → K
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  compactControl :
    letI : TopologicalSpace K := topologicalSpaceK
    CompactReferenceMetricTensorFamilyData K metric
  D : ℝ
  meanScalarFloor : ℝ
  covariantDerivativeRegularity : ∀ t : Ici (0 : ℝ),
    CovariantDerivative.ContMDiffCovariantDerivative (gt t.1).leviCivita 1
  meanScalarFloor_pos : 0 < meanScalarFloor
  flow : ∀ t : Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t.1 x
  jointMetricEntriesThree : ∀ t : Ici (0 : ℝ), ∀ x : M,
    MetricEntriesJointContDiffAt gt t.1 x 3
  differentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1
  differentiateMovingVolume : ∀ t : Ici (0 : ℝ),
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1
  scalarVarianceEnergyDomination : ∀ t : Ici (0 : ℝ),
    normalizedFlowScalarVarianceTrack gt t.1 ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1
  finiteTracelessRicciEnergy :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0)
  covariantRicciDerivativeNormBound :
    UniformCovariantRicciDerivativeNormBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1) D
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)

/-- Fixed-target provider quantified only over the smooth instances selected
by the noncomputable atlas bridge.  The Borel measurable structure is
installed canonically. -/
def FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M

/-- The selected-atlas analytic package reaches the direct-sample sphere
endpoint while leaving unit-curvature recognition explicit. -/
theorem NormalizedFlowSphereMeanScalarAnalyticData3.sphereConclusion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : NormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  letI : Nonempty data.K :=
    ⟨data.parameter ⟨0, by simp⟩⟩
  letI : ∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t.1).leviCivita 1 :=
    data.covariantDerivativeRegularity
  obtain ⟨C, _hC, hScalarBound⟩ :=
    exists_pos_uniform_abs_scalarAt_bound_of_compact_joint_scalar
      data.metric data.scalarJointContinuous
  have hMeanUpper : ∀ t : Ici (0 : ℝ),
      meanScalar (data.gt t.1) ≤ C := by
    intro t
    have hMetricMeanUpper :
        meanScalar (data.metric (data.parameter t)) ≤ C :=
      meanScalar_le_of_forall_scalarAt_le
        (data.metric (data.parameter t)) C fun x ↦
          (le_abs_self _).trans (hScalarBound (data.parameter t) x)
    simpa only [data.realizesFlow t] using hMetricMeanUpper
  exact
    sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      data.gt data.metric data.parameter data.realizesFlow
      data.compactControl data.meanScalarFloor_pos data.flow
      data.jointMetricEntriesThree
      data.differentiateMovingTotalScalar data.differentiateMovingVolume
      data.scalarVarianceEnergyDomination hMeanUpper
      data.finiteTracelessRicciEnergy data.covariantRicciDerivativeNormBound
      data.meanScalarLower
      data.scalarJointContinuous data.tracelessRicciNormSqJointContinuous
      unitRecognition

/-- Direct noncircular fixed-target sphere conclusion for the direct-sample
mean-scalar route from one selected proof-bearing smooth-transition atlas.

The atlas package is exactly what the normalized-flow endpoint consumes:
`isManifold_of_contDiffOn` constructs the smooth-manifold instance, while
compactness and simple connectivity construct second countability and
connectedness.  No `C¹` atlas, universal atlas-upgrade function, or
recognition theorem participates in atlas selection. -/
theorem sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_unitRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (smoothData : CInfinityLocalTransitionAtlasData3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (unitRecognition :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  refine normalizedFlowTarget_elim_of_cInfinityLocalTransitionAtlasData3
    smoothData ?_
  intro _charted _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact analytic.sphereConclusion unitRecognition

/-- Compatibility corollary for the Moise-shaped split smoothability
boundary.

The local transition-smoothing premise is used only to construct the selected
smooth atlas.  Analytic data and unit-curvature recognition are quantified
under that atlas and remain independent inputs. -/
theorem sphereConclusion_of_admitsSurgeryModelSmoothStructure_of_localTransitionSmoothing_of_normalizedFlowMeanScalarAnalyticData_of_unitRecognition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (admits : AdmitsSurgeryModelSmoothStructure M)
    (localSmoothing : C1AtlasLocalTransitionSmoothing3 M)
    (analytic :
      FixedTargetNormalizedFlowSphereMeanScalarAnalyticData3.{u, v} M)
    (unitRecognition :
      ∀ [ChartedSpace (ClosedSmoothModel 3) M]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
        [SecondCountableTopology M] [ConnectedSpace M],
          UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  rcases admits with ⟨c1Atlas, c1Manifold⟩
  letI : ChartedSpace ThreeManifoldModel M := c1Atlas
  exact
    sphereConclusion_of_cInfinityLocalTransitionAtlasData_of_normalizedFlowMeanScalarAnalyticData_of_unitRecognition
      (localSmoothing c1Atlas c1Manifold) analytic unitRecognition

end Poincare
