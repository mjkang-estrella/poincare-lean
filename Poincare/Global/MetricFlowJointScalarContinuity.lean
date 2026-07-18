import Poincare.Global.MetricFlowJointScalarTraceZoneBridge

/-!
# Scalar continuity on metric-entry regularity regions

The cutoff-one scalar trace bridge gives pointwise joint space-time continuity
from joint `C³` metric entries.  This file packages that local theorem as
`ContinuousOn` statements, including the time-shifted compact slabs consumed
by the finite-extinction comparison argument.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Joint metric-entry regularity at every point of a region makes intrinsic
scalar curvature jointly continuous on that region. -/
theorem continuousOn_scalarAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {S : Set (ℝ × M)}
    (hJoint : ∀ p ∈ S, MetricEntriesJointContDiffAt gt p.1 p.2 3) :
    ContinuousOn (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) S := by
  intro p hp
  exact (continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
    (hJoint p hp)).continuousWithinAt

/-- The form used on one surgery segment: metric-entry regularity at the
shifted physical times `t₀ + τ` supplies scalar continuity on the compact
relative-time slab `[0,T] × M`. -/
theorem continuousOn_scalarAt_timeShift_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
    (hJoint : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ y : M,
      MetricEntriesJointContDiffAt gt (t₀ + τ) y 3) :
    ContinuousOn
      (fun p : ℝ × M ↦ (gt (t₀ + p.1)).scalarAt p.2)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
  intro p hp
  have hscalar :=
    continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
      (hJoint p.1 hp.1 p.2)
  have hshift : ContinuousAt
      (fun q : ℝ × M ↦ (t₀ + q.1, q.2)) p :=
    (continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd
  exact (ContinuousAt.comp'
    (f := fun q : ℝ × M ↦ (t₀ + q.1, q.2))
    (g := fun q : ℝ × M ↦ (gt q.1).scalarAt q.2)
    (x := p) hscalar hshift).continuousWithinAt

end Poincare
