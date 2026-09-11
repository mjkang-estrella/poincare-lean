import Poincare.Global.NormalizedFlowHausdorffPartitionStokes
import Poincare.Global.HamiltonChartDensityLocalDomination

/-!
# Open-chart data for closed Laplacian Stokes

The constructors below supply genuine chart measures and compactly supported
coordinate scalars. Coordinate coefficient identities remain explicit inputs
to the final partial constructor.
-/

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesProducer

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The full inverse-chart measure is the Riemannian measure on its open source. -/
theorem openChart_measure (g : ClosedSmoothRiemannianMetric n M) (p : M) :
    HausdorffChartDensityEquality g (extChartAt I p).target
      (inverseExtendedChartParametrization (n := n) p)
      (extChartAt I p).source (inverseChartPullbackVolumeDensity g p) := by
  have hrange : Set.range (inverseExtendedChartParametrization (n := n) p) =
      (extChartAt I p).source := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (extChartAt I p).map_target z.2
    · intro hx
      refine ⟨⟨extChartAt I p x, (extChartAt I p).map_source hx⟩, ?_⟩
      exact (extChartAt I p).left_inv hx
  simpa only [hrange] using inverseChart_hausdorffChartDensityEquality g p

end Poincare.ClosedLaplacianStokesProducer
