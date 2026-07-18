import Poincare.Global.SmoothabilityProofBearingAtlasUpgrade
import Poincare.Global.NormalizedFlowFullyAssembledEnergyEndpoint
import Poincare.Global.CartanAtlasRealizedEndpointTransport

/-!
# End-to-end completion from proof-bearing inputs

This module replaces the three proposition-shaped inputs of
`SmoothabilityExistenceBridge` by the strongest constructive interfaces
currently available in the repository:

* one-point recognition transports an actual `C∞` charted-space instance;
* raw normalized-flow, Hausdorff-density, compact-flux, differential-decay,
  and compact-parameter data construct the reduced Hamilton core; and
* explicit strict-factor endpoint transports construct the compatible Cartan
  atlas, with terminal equality derived from the recorded finite insertion
  chain.

The universal raw-flow record below deliberately stores no
`HamiltonConvergencePinchedLimit3Core`.  Likewise, the final theorems assume
neither `UniversalC1ToCInfinityAtlasUpgrade3` nor
`UnitCurvatureCompatibleCartanAtlas3`.  Those three former boundary
propositions are constructed in the proof.

The smoothability input remains honest about the current repository boundary:
its proof-bearing construction is a homeomorphism to the one-point
compactification model.  That recognition datum is already as strong as the
topological conclusion; this file does not present it as an independent proof
of Moise smoothing.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/--
Raw data consumed by the fully assembled normalized-flow endpoint on one
closed smooth simply connected three-manifold.

The measurable structure is fixed canonically to the Borel measurable space.
The compact parameter space is allowed to depend on the target manifold.  All
other fields exactly expose the hypotheses of
`hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_meanEnergy_parameterization`.
-/
structure FullyAssembledNormalizedFlowRawData
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
  compactFlux : GlobalFiniteHausdorffChartLaplacianFlux
    hausdorffVolume (fun t y ↦ (gt t).scalarAt y)
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
  scalarLowerConstant : ℝ
  scalarLowerConstant_pos : 0 < scalarLowerConstant
  scalarLower : ∀ t : ℝ, ∀ x : M,
    scalarLowerConstant ≤ (gt t).scalarAt x

/--
The sharper fully assembled raw endpoint.  Its geometric, analytic, flux, and
compact-parameter fields are identical to
`FullyAssembledNormalizedFlowRawData`; the uniform all-time pointwise scalar
floor is replaced by positivity of the actual limiting mean scalar.
-/
structure FullyAssembledNormalizedFlowMeanLimitPositiveRawData
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
  compactFlux : GlobalFiniteHausdorffChartLaplacianFlux
    hausdorffVolume (fun t y ↦ (gt t).scalarAt y)
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

/-- The raw record constructs, rather than stores, the reduced Hamilton core. -/
theorem FullyAssembledNormalizedFlowRawData.hamiltonConvergenceCore
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : FullyAssembledNormalizedFlowRawData.{u, v} M) :
    HamiltonConvergencePinchedLimit3Core M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1 :=
    data.covariantDerivativeRegularity
  exact
    hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_meanEnergy_parameterization
      data.flow data.hausdorffVolume data.scalarDomination
      data.jointMetricEntries data.compactFlux data.dissipationDerivative
      data.rate_pos data.hasDissipationDerivative data.differentialInequality
      data.metric data.parameter data.realizesFlow data.invariantContinuous
      data.scalarLowerConstant_pos data.scalarLower

/-- The sharper raw record constructs the reduced Hamilton core directly from
positivity of the limiting mean scalar. -/
theorem FullyAssembledNormalizedFlowMeanLimitPositiveRawData.hamiltonConvergenceCore
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data :
      FullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v} M) :
    HamiltonConvergencePinchedLimit3Core M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1 :=
    data.covariantDerivativeRegularity
  exact
    hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_meanEnergy_parameterization_of_meanLimitPos
      data.flow data.hausdorffVolume data.scalarDomination
      data.jointMetricEntries data.compactFlux data.dissipationDerivative
      data.rate_pos data.hasDissipationDerivative data.differentialInequality
      data.metric data.parameter data.realizesFlow data.invariantContinuous
      data.meanLimitPositive

/-- A uniform positive scalar floor implies positivity of the limiting mean
scalar after the differential-decay fields have supplied finite absolute
dissipation.  This makes the original raw record a concrete specialization of
the sharper record. -/
theorem FullyAssembledNormalizedFlowRawData.meanLimitPositive
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : FullyAssembledNormalizedFlowRawData.{u, v} M) :
    0 < normalizedMeanScalarLimit data.gt := by
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1 :=
    data.covariantDerivativeRegularity
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity data.gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
      data.jointMetricEntries
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes
        (data.gt t) (fun y ↦ (data.gt t).scalarAt y) :=
    data.compactFlux.closedLaplacianStokes
  let hHausdorffScalar :
      GlobalFiniteHausdorffChartScalarVariation data.gt :=
    data.scalarDomination.toScalarVariation
      data.flow (by norm_num) hLichnerowicz hStokes
  have hFiniteDissipation :
      IntegrableOn
        (normalizedMeanScalarAbsoluteVarianceDissipation data.gt) (Ici 0) :=
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
      data.gt data.dissipationDerivative data.rate_pos
      data.hasDissipationDerivative data.differentialInequality
  have hMeanTendsto :=
    tendsto_meanScalar_normalizedMeanScalarLimit_of_normalizedFlow_finiteAbsoluteDissipation
      data.gt data.flow
      (hHausdorffScalar.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        data.flow hLichnerowicz hStokes)
      (hHausdorffScalar.hasDerivAt_totalVolume_of_normalizedFlow data.flow)
      hFiniteDissipation
  have hMeanLimitLower :
      data.scalarLowerConstant ≤ normalizedMeanScalarLimit data.gt :=
    ge_of_tendsto hMeanTendsto <| Eventually.of_forall fun t ↦
      le_meanScalar_of_forall_le_scalarAt
        (data.gt t) data.scalarLowerConstant (data.scalarLower t)
  exact data.scalarLowerConstant_pos.trans_le hMeanLimitLower

/-- Forget the stronger uniform scalar floor after deriving the weaker sharp
limiting-mean positivity field. -/
def FullyAssembledNormalizedFlowRawData.toMeanLimitPositive
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : FullyAssembledNormalizedFlowRawData.{u, v} M) :
    FullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v} M where
  K := data.K
  topologicalSpaceK := data.topologicalSpaceK
  compactSpaceK := data.compactSpaceK
  gt := data.gt
  covariantDerivativeRegularity := data.covariantDerivativeRegularity
  flow := data.flow
  hausdorffVolume := data.hausdorffVolume
  scalarDomination := data.scalarDomination
  jointMetricEntries := data.jointMetricEntries
  compactFlux := data.compactFlux
  dissipationDerivative := data.dissipationDerivative
  rate := data.rate
  rate_pos := data.rate_pos
  hasDissipationDerivative := data.hasDissipationDerivative
  differentialInequality := data.differentialInequality
  metric := data.metric
  parameter := data.parameter
  realizesFlow := data.realizesFlow
  invariantContinuous := data.invariantContinuous
  meanLimitPositive := data.meanLimitPositive

/-- Manifold-dependent raw normalized-flow data on every target quantified by
the smooth global Poincare statement. -/
def UniversalFullyAssembledNormalizedFlowRawData : Type (max (u + 1) (v + 1)) :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      FullyAssembledNormalizedFlowRawData.{u, v} M

/-- Manifold-dependent raw normalized-flow data with the sharp positive
limiting-mean premise on every smooth Poincare target. -/
def UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData :
    Type (max (u + 1) (v + 1)) :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      FullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v} M

/-- The universal raw-flow provider constructs the universal Hamilton core. -/
theorem universalHamiltonConvergenceCore_of_fullyAssembledNormalizedFlowRawData
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v}) :
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

/-- The universal sharp raw-flow provider constructs the universal Hamilton
core from limiting-mean positivity. -/
theorem universalHamiltonConvergenceCore_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData
    (raw :
      UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v}) :
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

/-- The original universal scalar-floor provider is a concrete specialization
of the sharp limiting-mean provider. -/
def UniversalFullyAssembledNormalizedFlowRawData.toMeanLimitPositive
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v}) :
    UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v} := by
  intro M _top _t2 _second _charted _manifold _compact _connected _simply
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact (raw M).toMeanLimitPositive

/-- Explicit strict finite-factor endpoint transports on every smooth target
and every unit constant-curvature metric. -/
def UniversalStrictFactorEndpointTransportAtlasData :
    Type (u + 1) :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CartanAtlasRealizedEndpointTransport.StrictFactorEndpointTransportAtlasData g

/-- The sharp positive-mean-limit raw flow data and strict-factor endpoint
transport close the smooth global Poincare statement without an all-time
pointwise scalar floor. -/
theorem poincareConjecture_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
    (raw :
      UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  CartanAtlasRealizedEndpointTransport.poincareConjecture_of_hamiltonConvergenceCore_of_strictFactorEndpointTransport
    (universalHamiltonConvergenceCore_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData
      raw)
    transport

/-- Raw normalized-flow data and explicit strict-factor endpoint transport
close the smooth global Poincare statement without assuming either the
Hamilton core or a compatible Cartan atlas. -/
theorem poincareConjecture_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  CartanAtlasRealizedEndpointTransport.poincareConjecture_of_hamiltonConvergenceCore_of_strictFactorEndpointTransport
    (universalHamiltonConvergenceCore_of_fullyAssembledNormalizedFlowRawData raw)
    transport

/-- Sharp end-to-end canonical project statement.  The Hamilton construction
uses positivity only of the limiting mean scalar; no uniform pointwise scalar
lower bound is present in the input. -/
theorem poincareConjectureStatement_of_onePointRecognition_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_onePointRecognition recognize)
    (poincareConjecture_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
      raw transport)

/-- The sharp raw inputs expose both the smooth global theorem and canonical
topological project statement. -/
theorem poincareConjecture_and_statement_of_onePointRecognition_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} ∧ PoincareConjectureStatement.{u} :=
  ⟨poincareConjecture_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
      raw transport,
    poincareConjectureStatement_of_onePointRecognition_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_strictFactorEndpointTransport
      recognize raw transport⟩

/--
End-to-end canonical project statement from the three proof-bearing inputs.

The selected smooth atlas is transported from `recognize`; the Hamilton core
is assembled from every raw field in `raw`; and the compatible Cartan atlas is
constructed from `transport` by finite strict-factor concatenation.
-/
theorem poincareConjectureStatement_of_onePointRecognition_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_onePointRecognition recognize)
    (poincareConjecture_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
      raw transport)

/-- The same raw inputs expose both the smooth global theorem and the
canonical topological project theorem in one result. -/
theorem poincareConjecture_and_statement_of_onePointRecognition_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} ∧ PoincareConjectureStatement.{u} :=
  ⟨poincareConjecture_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
      raw transport,
    poincareConjectureStatement_of_onePointRecognition_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
      recognize raw transport⟩

/-- A proof-bearing smoothability package supplies the actual transported
smooth atlas through its earliest PL-smoothing-existence recognition field;
its already-packaged `smoothManifold` field is not used. -/
theorem poincareConjectureStatement_of_smoothabilityPackage_plSmoothingExistence_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
    (package : SmoothabilityPackage.{u})
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_smoothabilityPackage_plSmoothingExistence
      package)
    (poincareConjecture_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
      raw transport)

/-- Universal finite extinction plus proof-bearing topology extraction is an
alternative source of the transported smooth atlas.  The raw Hamilton and
strict-factor Cartan inputs remain explicit. -/
theorem poincareConjectureStatement_of_universalFiniteExtinction_and_topologyPackage_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u})
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v})
    (transport : UniversalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_universalFiniteExtinction_and_topologyPackage
      finiteExtinction package)
    (poincareConjecture_of_fullyAssembledNormalizedFlowRawData_of_strictFactorEndpointTransport
      raw transport)

end Poincare
