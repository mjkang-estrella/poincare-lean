import Poincare.Global.RiemannianContext

/-!
# Completeness of the induced Riemannian distance on closed manifolds

The Hopf–Rinow side of the space-form program needs "closed implies
complete".  For the repository's induced metric-space structure this is pure
topology: the Riemannian emetric construction reuses the manifold topology,
so compactness gives completeness of the induced uniformity outright.  We
record the statement in the `letI` form consumed downstream.
-/

noncomputable section

open scoped Manifold ContDiff

universe u

namespace Poincare

namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/--
The metric space induced by a closed smooth Riemannian metric on a compact
connected manifold is complete.
-/
theorem toMetricSpace_completeSpace [T2Space M] [CompactSpace M]
    [ConnectedSpace M] (g : ClosedSmoothRiemannianMetric n M) :
    letI : MetricSpace M := g.toMetricSpace
    CompleteSpace M := by
  letI : MetricSpace M := g.toMetricSpace
  exact inferInstance

/--
The emetric space induced by a closed smooth Riemannian metric on a compact
manifold is complete.
-/
theorem toEMetricSpace_completeSpace [T2Space M] [CompactSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    letI : EMetricSpace M := g.toEMetricSpace
    CompleteSpace M := by
  letI : EMetricSpace M := g.toEMetricSpace
  exact inferInstance

end ClosedSmoothRiemannianMetric

end Poincare
