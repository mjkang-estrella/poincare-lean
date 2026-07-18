import Poincare.Global.NormalizedFlowHausdorffClosedRangeEndpoint
import Poincare.Global.MetricFlowJointIteratedConnectionRegularity

/-!
# Hausdorff point coverage and spatial/mixed Lichnerowicz regularity

The original all-time Lichnerowicz package contains a global
`TimeDifferentiableAt` field.  The Hausdorff chart package already records
time differentiability on every inverse-chart image, but its measure equality
does not by itself imply that those images cover the manifold pointwise.

This file adds that missing geometric fact explicitly: every recorded
manifold piece is covered by the range of its corresponding inverse chart.
Together with `pieces_cover`, this proves global time differentiability.  The
remaining Lichnerowicz input can then be weakened to a spatial/mixed package
with no time-differentiability field.

The final section also closes a second boundary with existing theorems:
global joint `C³` metric entries already imply time differentiability, spatial
`C²` regularity of the time variation, mixed derivative commutation, and
`MetricFlowRegularAt`.  Thus no new black-box smoothness proposition is needed
for that route.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section PointwiseHausdorffCoverage

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- A strengthened global Hausdorff scalar-variation package whose recorded
inverse chart for each piece really covers that piece pointwise.

This field is intentionally separate from `chartMeasure`: equality of a
pushforward measure with a restricted volume measure does not imply
surjectivity of the underlying map. -/
structure PointwiseCoveredGlobalFiniteHausdorffChartScalarVariation
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  variation : GlobalFiniteHausdorffChartScalarVariation gt
  inverseChart_covers_piece : ∀ t : ℝ,
    ∀ i : Fin (variation.volumeVariation.decomposition t).chartCount,
      ∀ x ∈ (variation.volumeVariation.decomposition t).manifoldPiece i,
        ∃ z : (variation.volumeVariation.decomposition t).coordinateDomain i,
          (variation.volumeVariation.decomposition t).inverseChart i z = x

omit [SecondCountableTopology M] in
/-- Pointwise inverse-chart coverage and `pieces_cover` upgrade the
Hausdorff package's chartwise time differentiability to every manifold point.
-/
theorem PointwiseCoveredGlobalFiniteHausdorffChartScalarVariation.timeDifferentiable
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : PointwiseCoveredGlobalFiniteHausdorffChartScalarVariation gt)
    (t : ℝ) (x : M) :
    TimeDifferentiableAt gt t x := by
  let D := H.variation.volumeVariation.decomposition t
  have hx : x ∈ ⋃ i, D.manifoldPiece i := by
    rw [D.pieces_cover]
    exact mem_univ x
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨z, hz⟩ := H.inverseChart_covers_piece t i x hxi
  rw [← hz]
  exact H.variation.volumeVariation.timeDifferentiable t i z

end PointwiseHausdorffCoverage

section SpatialMixedRegularity

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The genuinely spatial/mixed portion of automatic Lichnerowicz assembly.
Global time differentiability is absent and will be supplied by pointwise
Hausdorff chart coverage. -/
structure GlobalLichnerowiczSpatialMixedRegularity
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) : Prop where
  nearMetricFlowRegularity : ∀ t : ℝ, ∀ x : M,
    ∀ᶠ y in nhds x,
      MetricFlowRegularAt gt t y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun s ↦
              extDerivFun
                (fun z : M ↦ (gt s).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t z (extend E b z) (extend E c z))
              y a) t)
  timeVariationEntries : ∀ t : ℝ, ∀ y : M,
    TimeVariationExtContMDiffAt gt t y 2

/-- Assemble the former all-time Lichnerowicz package from explicit
Hausdorff point coverage and the weaker spatial/mixed regularity package. -/
def GlobalLichnerowiczSpatialMixedRegularity.toAssemblyRegularity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (S : GlobalLichnerowiczSpatialMixedRegularity gt)
    (H : PointwiseCoveredGlobalFiniteHausdorffChartScalarVariation gt) :
    GlobalLichnerowiczAssemblyRegularity gt where
  timeDifferentiable := H.timeDifferentiable
  nearMetricFlowRegularity := S.nearMetricFlowRegularity
  timeVariationEntries := S.timeVariationEntries

end SpatialMixedRegularity

section JointMetricEntries

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Existing joint `C³` metric-entry regularity constructs the entire
spatial/mixed package.  In particular, its time derivative is spatially `C²`;
this is not retained as an independent black-box premise. -/
def globalLichnerowiczSpatialMixedRegularity_of_jointMetricEntriesThree
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3) :
    GlobalLichnerowiczSpatialMixedRegularity gt where
  nearMetricFlowRegularity t _x :=
    Eventually.of_forall fun y ↦
      ⟨metricFlowRegularAt_of_metricEntriesJointContDiffAt_three
          (x := y) (hJoint t),
        metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
          ((hJoint t y).of_le (by norm_num))⟩
  timeVariationEntries t y :=
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint t y)

/-- Joint `C³` metric entries also supply global time differentiability, so
they directly construct the complete Lichnerowicz assembly package. -/
def globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3) :
    GlobalLichnerowiczAssemblyRegularity gt where
  timeDifferentiable t y :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint t y).of_le (by norm_num))
  nearMetricFlowRegularity :=
    (globalLichnerowiczSpatialMixedRegularity_of_jointMetricEntriesThree
      hJoint).nearMetricFlowRegularity
  timeVariationEntries :=
    (globalLichnerowiczSpatialMixedRegularity_of_jointMetricEntriesThree
      hJoint).timeVariationEntries

end JointMetricEntries

section DimensionThreeEndpoints

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- LSC endpoint from pointwise-covered Hausdorff charts and the weaker
spatial/mixed Lichnerowicz package. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_pointwiseCoveredHausdorffSpatialMixedRegularity_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff :
      PointwiseCoveredGlobalFiniteHausdorffChartScalarVariation gt)
    (hSpatialMixed : GlobalLichnerowiczSpatialMixedRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_lscCompactness
      hFlow hHausdorff.variation
      (hSpatialMixed.toAssemblyRegularity hHausdorff)
      hStokes hFiniteDissipation hCompact hc hScalarLower

/-- Closed mean-energy-range endpoint from the same weaker package. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_pointwiseCoveredHausdorffSpatialMixedRegularity_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff :
      PointwiseCoveredGlobalFiniteHausdorffChartScalarVariation gt)
    (hSpatialMixed : GlobalLichnerowiczSpatialMixedRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff.variation
      (hSpatialMixed.toAssemblyRegularity hHausdorff)
      hStokes hFiniteDissipation hRangeClosed hc hScalarLower

/-- Exponential decay version of the pointwise-covered closed-range
endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_pointwiseCoveredHausdorffSpatialMixedRegularity_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff :
      PointwiseCoveredGlobalFiniteHausdorffChartScalarVariation gt)
    (hSpatialMixed : GlobalLichnerowiczSpatialMixedRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate c : ℝ} (hrate : 0 < rate) (hc : 0 < c)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff.variation
      (hSpatialMixed.toAssemblyRegularity hHausdorff)
      hStokes hDissipationMeasurable hrate hc hDecay hRangeClosed hScalarLower

/-- Joint `C³` metric entries eliminate the entire separate Lichnerowicz
package in the LSC endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_lscCompactness
      hFlow hHausdorff
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
      hStokes hFiniteDissipation hCompact hc hScalarLower

/-- Joint `C³` metric entries likewise eliminate the Lichnerowicz package in
the closed mean-energy-range endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
      hStokes hFiniteDissipation hRangeClosed hc hScalarLower

end DimensionThreeEndpoints

end Poincare
