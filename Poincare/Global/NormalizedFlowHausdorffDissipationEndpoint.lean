import Poincare.Global.NormalizedFlowAbsoluteDissipation
import Poincare.Global.HausdorffVolumeFirstVariation

/-!
# Absolute-dissipation endpoint with actual Hausdorff volume variation

The finite-chart density package now supplies the moving-volume derivative
required by the normalized-flow energy argument.  The resulting theorem keeps
only the local Hausdorff area-formula package, moving total-scalar derivative,
finite absolute dissipation, scalar-energy compactness, and positivity.
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

/-- The Hausdorff chart-density variation theorem discharges moving-volume
differentiation in the absolute-dissipation Hamilton endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartDensity_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hHausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_scalarLower
      gt hFlow hDifferentiateMovingTotalScalar
        (fun t ↦ hHausdorffVolume.hasDerivAt_totalVolume t
          (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
            (hFlow t) (by norm_num)))
        hFiniteDissipation hCompact hc hScalarLower

end Poincare
