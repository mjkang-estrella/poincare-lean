import Poincare.Global.NormalizedFlowPartitionFullyAssembledEnergyEndpoint
import Poincare.Global.ProofBearingEndToEndCompletion
import Poincare.Global.CartanAtlasAutomaticAnchorAlignment

/-!
# Proof-bearing end-to-end completion from subordinate coordinate Stokes

This module adapts the corrected partition-of-unity Stokes route to the
proof-bearing raw-data and end-to-end interfaces.  Each provider is recorded
exactly once: moving Hausdorff scalar domination, joint metric regularity,
subordinate coordinate geometry, differential decay, invariant compactness,
and limiting-mean positivity.  Derived packages such as
`ClosedLaplacianStokes`, Lichnerowicz regularity, finite dissipation, and the
Hamilton core are conclusions rather than duplicated fields.

The existing proof-bearing smoothability and strict-factor Cartan transport
interfaces are reused unchanged.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanAtlasAutomaticAnchorAlignment

/-- Raw normalized-flow data whose Stokes provider is a genuine finite smooth
subordinate coordinate partition.

This is the positive-mean-limit proof-bearing counterpart of
`FullyAssembledNormalizedFlowMeanLimitPositiveRawData`.  It does not also
retain the older per-disjoint-piece compact-flux provider. -/
structure SubordinatePartitionNormalizedFlowMeanLimitPositiveRawData
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
  covariantDerivativeRegularity :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1
  flow : ∀ t : ℝ, ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  hausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt
  scalarDomination :
    GlobalFiniteHausdorffChartScalarDomination hausdorffVolume
  jointMetricEntries : ∀ t : ℝ, ∀ y : M,
    MetricEntriesJointContDiffAt gt t y 3
  subordinateGeometry : GlobalFiniteSubordinateHausdorffLaplacianGeometry
    gt (fun t y ↦ (gt t).scalarAt y)
  dissipationDerivative : ℝ → ℝ
  rate : ℝ
  rate_pos : 0 < rate
  hasDissipationDerivative : ∀ t ∈ Ici (0 : ℝ),
    HasDerivAt
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (dissipationDerivative t) t
  differentialInequality : ∀ t ∈ Ici (0 : ℝ),
    dissipationDerivative t ≤
      -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : ℝ → K
  realizesFlow : ∀ t : ℝ, metric (parameter t) = gt t
  invariantContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k))
  meanLimitPositive : 0 < normalizedMeanScalarLimit gt

/-- The subordinate-partition raw record constructs the reduced Hamilton
core; it does not store that conclusion. -/
theorem SubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.hamiltonConvergenceCore
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      SubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v} M) :
    HamiltonConvergencePinchedLimit3Core M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1 :=
    data.covariantDerivativeRegularity
  exact
    hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesSubordinatePartition_of_compact_meanEnergy_parameterization_of_meanLimitPos
      data.flow data.hausdorffVolume data.scalarDomination
      data.jointMetricEntries data.subordinateGeometry
      data.dissipationDerivative data.rate_pos
      data.hasDissipationDerivative data.differentialInequality
      data.metric data.parameter data.realizesFlow data.invariantContinuous
      data.meanLimitPositive

/-- Manifold-dependent subordinate-partition raw data on every target of the
smooth global Poincare statement. -/
def UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData :
    Type (max (u + 1) (v + 1)) :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      SubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v} M

/-- The universal raw provider constructs the universal Hamilton core through
the subordinate-partition endpoint. -/
theorem universalHamiltonConvergenceCore_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData
    (raw :
      UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v}) :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M]
      [ChartedSpace (ClosedSmoothModel 3) M]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
      [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
        HamiltonConvergencePinchedLimit3Core M := by
  intro M _top _t2 _second _charted _manifold _compact _connected _simply
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact (raw M).hamiltonConvergenceCore

/-- Subordinate-partition raw flow data and the existing proof-bearing strict
factor endpoint transport prove the smooth global Poincare conjecture. -/
theorem poincareConjecture_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
    (raw :
      UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  CartanAtlasRealizedEndpointTransport.poincareConjecture_of_hamiltonConvergenceCore_of_strictFactorEndpointTransport
    (universalHamiltonConvergenceCore_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData
      raw)
    transport

/-- One-point recognition supplies smoothability while the corrected raw flow
and strict-factor transport supply the smooth global theorem. -/
theorem poincareConjectureStatement_of_onePointRecognition_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_onePointRecognition recognize)
    (poincareConjecture_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
      raw transport)

/-- The same proof-bearing providers expose both the smooth global theorem and
the canonical topological project statement. -/
theorem poincareConjecture_and_statement_of_onePointRecognition_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} ∧ PoincareConjectureStatement.{u} :=
  ⟨poincareConjecture_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
      raw transport,
    poincareConjectureStatement_of_onePointRecognition_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
      recognize raw transport⟩

/-- The corrected subordinate-partition raw flow and the strong
constant-target strict-factor specialization conditionally prove the smooth
global Poincare conjecture.  Target coherence shows that this specialization
is not the general Cartan globalization boundary. -/
theorem poincareConjecture_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
    (raw :
      UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergenceCore_of_canonicalStrictFactorEndpointTransport
    (universalHamiltonConvergenceCore_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData
      raw)
    transport

/-- One-point recognition supplies smoothability while the corrected raw flow
and constant-target strict-factor specialization supply the smooth theorem. -/
theorem poincareConjectureStatement_of_onePointRecognition_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_onePointRecognition recognize)
    (poincareConjecture_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
      raw transport)

/-- The subordinate-partition inputs expose both statements under the same
strong constant-target strict-factor specialization. -/
theorem poincareConjecture_and_statement_of_onePointRecognition_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalSubordinatePartitionNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} ∧ PoincareConjectureStatement.{u} :=
  ⟨poincareConjecture_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
      raw transport,
    poincareConjectureStatement_of_onePointRecognition_of_subordinatePartitionNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
      recognize raw transport⟩

end Poincare
