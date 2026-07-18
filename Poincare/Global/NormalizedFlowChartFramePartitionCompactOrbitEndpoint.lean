import Poincare.Global.HausdorffChartFrameFirstVariation
import Poincare.Global.HausdorffScalarDensityDomination
import Poincare.Global.NormalizedFlowPartitionCompactOrbitEndpoint

/-!
# Normalized-flow endpoints from honest chart-frame density variation

`HausdorffChartFrameFirstVariation` replaces the legacy equality between an
actual coordinate density and `coordinateGramVolumeDensityAt` by the
frame-independent intrinsic first-variation identity.  This module carries
that correction through scalar-density domination and the dimension-three
normalized-flow endpoint.

The analytic scalar-density domination package is unchanged: it supplies
integrability, measurability, and an integrable bound.  Automatic
Lichnerowicz regularity supplies pointwise scalar differentiation, while
closed Laplacian Stokes supplies the remaining raw-integrand integrability.
Their composition constructs
`GlobalFiniteHausdorffChartFrameScalarVariation` without ever assuming
`UsesCoordinateGramDensity`.

The final theorem additionally combines automatic joint-`C³` Lichnerowicz
assembly, genuine subordinate-partition Stokes, differential dissipation
decay, and the actual compact metric-orbit closure interface.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section GlobalChartFrameDomination

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Scalar-density domination at every time relative to the corrected
chart-frame density-variation package.  This retains only the genuinely
analytic part of differentiating `density * scalarAt`.
-/
structure GlobalFiniteHausdorffChartFrameScalarDomination
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (V : GlobalFiniteHausdorffChartFrameDensityVariation gt) where
  scalarDomination : ∀ t : ℝ,
    FiniteChartScalarDensityDominationAt
      (V.decomposition t) (V.differentiation t)

/-- Automatic geometric scalar differentiation and closed Stokes upgrade
chart-frame scalar domination to the full corrected scalar-variation
package.
-/
def GlobalFiniteHausdorffChartFrameScalarDomination.toScalarVariation
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    {V : GlobalFiniteHausdorffChartFrameDensityVariation gt}
    (B : GlobalFiniteHausdorffChartFrameScalarDomination V)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hn : (n : ℝ) ≠ 0)
    (L : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y)) :
    GlobalFiniteHausdorffChartFrameScalarVariation gt where
  volumeVariation := V
  scalarDifferentiation t :=
    (B.scalarDomination t).toDominatedDifferentiation
      (fun _i _z s _hs ↦ L.hasDerivAt_scalar_deriv s _)
      (rawTotalScalarFirstVariation_integrand_integrable_of_normalizedFlow_of_lichnerowicz_of_stokes
        hFlow hn L hStokes t)

end GlobalChartFrameDomination

section DimensionThreeEndpoints

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

omit [SecondCountableTopology M] in
/-- The corrected chart-frame scalar package and automatic Lichnerowicz
assembly supply the normalized total-scalar derivative.
-/
theorem GlobalFiniteHausdorffChartFrameScalarVariation.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (H : GlobalFiniteHausdorffChartFrameScalarVariation gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (t : ℝ) :
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t :=
  H.hasDerivAt_totalScalar_energyNumerator hFlow (by norm_num)
    (fun s ↦ scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      (hFlow s) (hLichnerowicz.timeVariationEntries s))
    (fun s x ↦ hLichnerowicz.scalarVariation_stokes s x) hStokes t

omit [SecondCountableTopology M] in
/-- The corrected chart-frame volume package supplies the normalized moving
volume derivative without a selected-basis density equality.
-/
theorem GlobalFiniteHausdorffChartFrameScalarVariation.hasDerivAt_totalVolume_of_normalizedFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (H : GlobalFiniteHausdorffChartFrameScalarVariation gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (t : ℝ) :
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t :=
  H.volumeVariation.hasDerivAt_totalVolume t
    (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
      (hFlow t) (by norm_num))

/-- Dimension-three LSC compactness endpoint using only corrected chart-frame
Hausdorff density variation and scalar-density domination.
-/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_of_globalLichnerowiczRegularity_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hHausdorffScalar : GlobalFiniteHausdorffChartFrameScalarVariation gt :=
    hScalarDomination.toScalarVariation
      hFlow (by norm_num) hLichnerowicz hStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_lscCompactness_of_scalarLower
      gt hFlow
      (hHausdorffScalar.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorffScalar.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      hFiniteDissipation hCompact hc hScalarLower

/-- Sharp finite-dissipation endpoint with corrected chart-frame Hausdorff
variation and compactness of the actual metric-orbit closure.
-/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_of_globalLichnerowiczRegularity_of_compact_metricOrbitClosure_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hHausdorffScalar : GlobalFiniteHausdorffChartFrameScalarVariation gt :=
    hScalarDomination.toScalarVariation
      hFlow (by norm_num) hLichnerowicz hStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_metricOrbitClosure_of_meanLimitPos
      gt hFlow
      (hHausdorffScalar.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorffScalar.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      hFiniteDissipation hOrbitCompact hInvariantContinuous hMeanLimitPos

/-- Fully assembled corrected chart-frame endpoint: joint `C³` metric
entries construct Lichnerowicz regularity, subordinate coordinate geometry
constructs Stokes, differential decay constructs finite dissipation, and the
actual orbit closure supplies invariant compactness.
-/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_of_compact_metricOrbitClosure_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_of_globalLichnerowiczRegularity_of_compact_metricOrbitClosure_of_meanLimitPos
      hFlow hHausdorffVolume hScalarDomination hLichnerowicz hStokes
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      hOrbitCompact hInvariantContinuous hMeanLimitPos

end DimensionThreeEndpoints

end Poincare
