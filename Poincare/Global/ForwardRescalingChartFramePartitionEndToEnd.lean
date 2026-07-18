import Poincare.Global.MetricRescaleFiniteAtlasForwardFlow
import Poincare.Global.NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint

/-!
# Forward unnormalized flow to the chart-frame Hamilton endpoint

This module composes the two forward-time bridges:

1. finite inverse-atlas area formulas prove the mean-scalar scaling law and
   turn a forward unnormalized Ricci flow, a time change, and the base-mean
   scale ODE into a normalized flow on `Ici 0`;
2. the forward chart-frame/subordinate-partition compact-orbit endpoint turns
   that normalized flow into `HamiltonConvergencePinchedLimit3Core`.

The theorem is end-to-end across the rescaling seam.  Inputs not yet produced
by that seam remain explicit on the normalized path: corrected Hausdorff
chart-frame density variation and scalar domination, joint `C³` metric
entries, subordinate-partition Stokes geometry, quantitative dissipation
decay, compactness of the metric-orbit closure, continuity of the two
consumed scalar invariants, and a positive scalar-curvature floor.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- End-to-end forward rescaling and Hamilton-convergence theorem.

The base flow is required only on its nonnegative ray.  The proved positivity
of `τ' = c⁻¹` and `τ(0)=0` ensure that every reached base time is still
nonnegative.  Finite-atlas area formulas identify the normalized scale ODE
with the stated base-mean ODE.  All remaining hypotheses are attached
directly to the resulting normalized path. -/
theorem hamiltonConvergencePinchedLimit3Core_of_forwardUnnormalizedRicciFlow_of_finiteAtlasBaseMeanRescaling_of_chartFramePartitionCompactOrbit
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (baseFlow : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (3 : ℝ)) * meanScalar (baseFlow (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (baseFlow (τ t)) (c t) (hc t ht))
    (hBaseVolume : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (baseFlow (τ t)) ≠ 0)
    (hBaseFlow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt baseFlow s x)
    (hBaseTimeDifferentiable : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt baseFlow s x)
    [∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).leviCivita 1]
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc)
        (fun t y ↦
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt
        (normalizedMeanScalarAbsoluteVarianceDissipation
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
        (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t)
    (hOrbitCompact : IsCompact
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    {scalarFloor : ℝ} (hScalarFloorPos : 0 < scalarFloor)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      scalarFloor ≤
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let normalizedFlow : ℝ → ClosedSmoothRiemannianMetric 3 M :=
    forwardTimeReparameterizedConstRescaling baseFlow τ c hc
  have hNormalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
    dsimp only [normalizedFlow]
    exact
      isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
        C baseFlow τ c hτ0 hc hτ hscaleBase harea hBaseVolume
        hBaseFlow hBaseTimeDifferentiable
  exact
    hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      (gt := normalizedFlow) hNormalizedFlow hHausdorffVolume
      hScalarDomination hJoint hPartitionGeometry D' hrate
      hDissipationDeriv hDifferentialInequality hOrbitCompact
      hInvariantContinuous hScalarFloorPos hScalarLower

/-- End-to-end forward rescaling theorem with an explicit exponential
absolute-dissipation estimate in place of a derivative/coercivity pair.

The estimate and its measurability premise are the exact analytic data used
to prove finite dissipation; no auxiliary derivative function is exposed. -/
theorem hamiltonConvergencePinchedLimit3Core_of_forwardUnnormalizedRicciFlow_of_finiteAtlasBaseMeanRescaling_of_exponentialDissipation_chartFramePartitionCompactOrbit
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (baseFlow : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (3 : ℝ)) * meanScalar (baseFlow (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (baseFlow (τ t)) (c t) (hc t ht))
    (hBaseVolume : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (baseFlow (τ t)) ≠ 0)
    (hBaseFlow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt baseFlow s x)
    (hBaseTimeDifferentiable : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt baseFlow s x)
    [∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).leviCivita 1]
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc)
        (fun t y ↦
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
      (MeasureTheory.volume.restrict (Ici 0)))
    {decayConstant rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t ≤
        decayConstant * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    {scalarFloor : ℝ} (hScalarFloorPos : 0 < scalarFloor)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      scalarFloor ≤
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let normalizedFlow : ℝ → ClosedSmoothRiemannianMetric 3 M :=
    forwardTimeReparameterizedConstRescaling baseFlow τ c hc
  have hNormalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
    dsimp only [normalizedFlow]
    exact
      isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
        C baseFlow τ c hτ0 hc hτ hscaleBase harea hBaseVolume
        hBaseFlow hBaseTimeDifferentiable
  exact
    hamiltonConvergencePinchedLimit3Core_of_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      (gt := normalizedFlow) hNormalizedFlow hHausdorffVolume
      hScalarDomination hJoint hPartitionGeometry hDissipationMeasurable
      hrate hDecay hOrbitCompact hInvariantContinuous hScalarFloorPos
      hScalarLower

/-- End-to-end exponential-decay theorem with no assembled-dissipation
measurability premise.  The sole extra time-regularity input is continuity of
the moving scalar-variance integral on the forward ray. -/
theorem hamiltonConvergencePinchedLimit3Core_of_forwardUnnormalizedRicciFlow_of_finiteAtlasBaseMeanRescaling_of_continuousScalarVariance_exponentialDissipation_chartFramePartitionCompactOrbit
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (baseFlow : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (3 : ℝ)) * meanScalar (baseFlow (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (baseFlow (τ t)) (c t) (hc t ht))
    (hBaseVolume : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (baseFlow (τ t)) ≠ 0)
    (hBaseFlow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt baseFlow s x)
    (hBaseTimeDifferentiable : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt baseFlow s x)
    [∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).leviCivita 1]
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc)
        (fun t y ↦
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt y))
    (hScalarVarianceContinuous : ContinuousOn
      (fun t : ℝ ↦
        ∫ x,
          ((forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x -
            meanScalar
              (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t)) ^ 2
          ∂(volumeMeasure
            (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t)))
      (Ici 0))
    {decayConstant rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t ≤
        decayConstant * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    {scalarFloor : ℝ} (hScalarFloorPos : 0 < scalarFloor)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      scalarFloor ≤
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let normalizedFlow : ℝ → ClosedSmoothRiemannianMetric 3 M :=
    forwardTimeReparameterizedConstRescaling baseFlow τ c hc
  have hNormalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
    dsimp only [normalizedFlow]
    exact
      isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
        C baseFlow τ c hτ0 hc hτ hscaleBase harea hBaseVolume
        hBaseFlow hBaseTimeDifferentiable
  exact
    hamiltonConvergencePinchedLimit3Core_of_continuousScalarVariance_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      (gt := normalizedFlow) hNormalizedFlow hHausdorffVolume
      hScalarDomination hJoint hPartitionGeometry hScalarVarianceContinuous
      hrate hDecay hOrbitCompact hInvariantContinuous hScalarFloorPos
      hScalarLower

/-- Highest finite-chart forward rescaling endpoint.  The opaque continuity
assumption for the moving scalar variance is replaced by an integrable,
time-uniform bound on each coordinate variance density in the finite
Hausdorff chart-frame decomposition. -/
theorem hamiltonConvergencePinchedLimit3Core_of_forwardUnnormalizedRicciFlow_of_finiteAtlasBaseMeanRescaling_of_finiteChartScalarVarianceDomination_exponentialDissipation_chartFramePartitionCompactOrbit
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (baseFlow : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (3 : ℝ)) * meanScalar (baseFlow (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (baseFlow (τ t)) (c t) (hc t ht))
    (hBaseVolume : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (baseFlow (τ t)) ≠ 0)
    (hBaseFlow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt baseFlow s x)
    (hBaseTimeDifferentiable : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt baseFlow s x)
    [∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).leviCivita 1]
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc)
        (fun t y ↦
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt y))
    (hScalarVarianceDomination : ∀ t ∈ Ici (0 : ℝ),
      FiniteChartScalarVarianceDensityDominationAt
        (hHausdorffVolume.differentiation t))
    {decayConstant rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t ≤
        decayConstant * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    {scalarFloor : ℝ} (hScalarFloorPos : 0 < scalarFloor)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      scalarFloor ≤
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let normalizedFlow : ℝ → ClosedSmoothRiemannianMetric 3 M :=
    forwardTimeReparameterizedConstRescaling baseFlow τ c hc
  have hNormalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
    dsimp only [normalizedFlow]
    exact
      isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
        C baseFlow τ c hτ0 hc hτ hscaleBase harea hBaseVolume
        hBaseFlow hBaseTimeDifferentiable
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteChartScalarVarianceDomination_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      (gt := normalizedFlow) hNormalizedFlow hHausdorffVolume
      hScalarDomination hJoint hPartitionGeometry hScalarVarianceDomination
      hrate hDecay hOrbitCompact hInvariantContinuous hScalarFloorPos
      hScalarLower

/-- Highest forward rescaling endpoint with the nonlinear moving-measure
regularity reduced to local uniform boundedness of `|R - mean R|`.  The
integrable chart-density majorants are now constructed from the existing
density derivative data. -/
theorem hamiltonConvergencePinchedLimit3Core_of_forwardUnnormalizedRicciFlow_of_finiteAtlasBaseMeanRescaling_of_centeredScalarLocalBound_exponentialDissipation_chartFramePartitionCompactOrbit
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (baseFlow : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (3 : ℝ)) * meanScalar (baseFlow (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (baseFlow (τ t)) (c t) (hc t ht))
    (hBaseVolume : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (baseFlow (τ t)) ≠ 0)
    (hBaseFlow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt baseFlow s x)
    (hBaseTimeDifferentiable : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt baseFlow s x)
    [∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).leviCivita 1]
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc)
        (fun t y ↦
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt y))
    (hCenteredScalarLocalBound :
      GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound
        hHausdorffVolume)
    {decayConstant rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t ≤
        decayConstant * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    {scalarFloor : ℝ} (hScalarFloorPos : 0 < scalarFloor)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      scalarFloor ≤
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let normalizedFlow : ℝ → ClosedSmoothRiemannianMetric 3 M :=
    forwardTimeReparameterizedConstRescaling baseFlow τ c hc
  have hNormalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
    dsimp only [normalizedFlow]
    exact
      isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
        C baseFlow τ c hτ0 hc hτ hscaleBase harea hBaseVolume
        hBaseFlow hBaseTimeDifferentiable
  exact
    hamiltonConvergencePinchedLimit3Core_of_centeredScalarLocalBound_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      (gt := normalizedFlow) hNormalizedFlow hHausdorffVolume
      hScalarDomination hJoint hPartitionGeometry hCenteredScalarLocalBound
      hrate hDecay hOrbitCompact hInvariantContinuous hScalarFloorPos
      hScalarLower

/-- Strongest forward rescaling endpoint at the scalar-variance continuity
boundary.  Joint `C³` regularity and the normalized-flow first-variation
identities now construct all local centered-scalar and chart-density
majorants, so only the genuine exponential dissipation estimate remains. -/
theorem hamiltonConvergencePinchedLimit3Core_of_forwardUnnormalizedRicciFlow_of_finiteAtlasBaseMeanRescaling_of_automaticScalarVarianceDomination_exponentialDissipation_chartFramePartitionCompactOrbit
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (baseFlow : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (3 : ℝ)) * meanScalar (baseFlow (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (baseFlow (τ t)) (c t) (hc t ht))
    (hBaseVolume : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (baseFlow (τ t)) ≠ 0)
    (hBaseFlow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt baseFlow s x)
    (hBaseTimeDifferentiable : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt baseFlow s x)
    [∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).leviCivita 1]
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc)
        (fun t y ↦
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt y))
    {decayConstant rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t ≤
        decayConstant * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    {scalarFloor : ℝ} (hScalarFloorPos : 0 < scalarFloor)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      scalarFloor ≤
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let normalizedFlow : ℝ → ClosedSmoothRiemannianMetric 3 M :=
    forwardTimeReparameterizedConstRescaling baseFlow τ c hc
  have hNormalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
    dsimp only [normalizedFlow]
    exact
      isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
        C baseFlow τ c hτ0 hc hτ hscaleBase harea hBaseVolume
        hBaseFlow hBaseTimeDifferentiable
  exact
    hamiltonConvergencePinchedLimit3Core_of_automaticScalarVarianceDomination_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      (gt := normalizedFlow) hNormalizedFlow hHausdorffVolume
      hScalarDomination hJoint hPartitionGeometry hrate hDecay
      hOrbitCompact hInvariantContinuous hScalarFloorPos hScalarLower

/-- Sequentially compact form of the strongest forward rescaling endpoint.
The orbit realization boundary is reduced from compactness plus continuity to
`IsSeqCompact` plus `SeqContinuous`, exactly matching the subsequence used by
the finite-dissipation argument. -/
theorem hamiltonConvergencePinchedLimit3Core_of_forwardUnnormalizedRicciFlow_of_finiteAtlasBaseMeanRescaling_of_automaticScalarVarianceDomination_exponentialDissipation_chartFramePartitionSeqCompactOrbit
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (baseFlow : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (3 : ℝ)) * meanScalar (baseFlow (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (baseFlow (τ t)) (c t) (hc t ht))
    (hBaseVolume : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (baseFlow (τ t)) ≠ 0)
    (hBaseFlow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt baseFlow s x)
    (hBaseTimeDifferentiable : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt baseFlow s x)
    [∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).leviCivita 1]
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation
      (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc)
        (fun t y ↦
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt y))
    {decayConstant rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation
          (forwardTimeReparameterizedConstRescaling baseFlow τ c hc) t ≤
        decayConstant * Real.exp ((-rate) * t))
    (hOrbitSeqCompact : IsSeqCompact
      (closure (Set.range
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc))))
    (hInvariantSeqContinuous :
      SeqContinuous (closedMetricMeanTracelessEnergyPair (M := M)))
    {scalarFloor : ℝ} (hScalarFloorPos : 0 < scalarFloor)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      scalarFloor ≤
        (forwardTimeReparameterizedConstRescaling baseFlow τ c hc t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let normalizedFlow : ℝ → ClosedSmoothRiemannianMetric 3 M :=
    forwardTimeReparameterizedConstRescaling baseFlow τ c hc
  have hNormalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt normalizedFlow t x := by
    dsimp only [normalizedFlow]
    exact
      isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
        C baseFlow τ c hτ0 hc hτ hscaleBase harea hBaseVolume
        hBaseFlow hBaseTimeDifferentiable
  exact
    hamiltonConvergencePinchedLimit3Core_of_automaticScalarVarianceDomination_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_seqCompact_metricOrbitClosure_of_scalarLower
      (gt := normalizedFlow) hNormalizedFlow hHausdorffVolume
      hScalarDomination hJoint hPartitionGeometry hrate hDecay
      hOrbitSeqCompact hInvariantSeqContinuous hScalarFloorPos hScalarLower

end Poincare
