import Poincare.Global.RiemannianContext
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Riemannian volume measure via Hausdorff measure

This module opens the global Riemannian volume route by taking the
`n`-dimensional Hausdorff measure of the metric space induced by a closed
smooth Riemannian metric.

The definition assumes `[MeasurableSpace M] [BorelSpace M]` instead of
constructing a local Borel measurable space in the return type.  The type
`MeasureTheory.Measure M` itself requires a measurable-space instance, and
`BorelSpace M` records that this instance is the Borel sigma algebra.  After
installing `g.toMetricSpace`, this is the Borel structure for the induced
Riemannian topology, which is definitionally the manifold topology in
Mathlib's Riemannian path-length construction.
-/

noncomputable section

open scoped Manifold ContDiff MeasureTheory

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/--
The Riemannian volume candidate on a closed smooth `n`-manifold: the
`n`-dimensional Hausdorff measure for the metric induced by `g`.
-/
def volumeMeasure (g : ClosedSmoothRiemannianMetric n M) :
    MeasureTheory.Measure M :=
  letI : MetricSpace M := g.toMetricSpace
  μH[(n : ℝ)]

@[simp]
theorem volumeMeasure_apply (g : ClosedSmoothRiemannianMetric n M)
    (s : Set M) :
    volumeMeasure g s =
      (letI : MetricSpace M := g.toMetricSpace
       (μH[(n : ℝ)] : MeasureTheory.Measure M) s) :=
  rfl

/--
Open sets are usable through the measurable-set API for `volumeMeasure`.
This is the Borel-measure sanity check supplied by Mathlib's Hausdorff
construction.
-/
theorem isOpen_nullMeasurableSet_volumeMeasure
    (g : ClosedSmoothRiemannianMetric n M) {s : Set M} (hs : IsOpen s) :
    MeasureTheory.NullMeasurableSet s (volumeMeasure g) :=
  hs.measurableSet.nullMeasurableSet

/-- In positive dimension, the Hausdorff route gives a nonatomic volume measure. -/
theorem volumeMeasure_noAtoms (g : ClosedSmoothRiemannianMetric n M)
    (hn : 0 < n) :
    MeasureTheory.NoAtoms (volumeMeasure g) := by
  letI : MetricSpace M := g.toMetricSpace
  dsimp [volumeMeasure]
  exact MeasureTheory.Measure.noAtoms_hausdorff M (by exact_mod_cast hn)

end Poincare
