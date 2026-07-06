import Poincare.Global.VolumeMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Reductions for finiteness of the induced Hausdorff volume

This file isolates the missing local metric comparison needed to prove
`IsFiniteMeasure (volumeMeasure g)`.

Mathlib supplies the measure-theoretic part: finite-dimensional Euclidean
compact sets have finite `μH[n]`, and Lipschitz images have controlled
Hausdorff measure.  The remaining geometric input is a pairwise Lipschitz
bound for inverse smooth charts into the Riemannian path metric.

The intended missing comparison lemma is:

```lean
theorem exists_compact_lipschitz_extChartAt_symm_image_nhds
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∃ s : Set (ClosedSmoothModel n),
      IsCompact s ∧
      (extChartAt (closedSmoothModelWithCorners n) x).symm '' s ∈ 𝓝 x ∧
      ∃ K : ℝ≥0,
        letI : MetricSpace M := g.toMetricSpace
        LipschitzOnWith K (extChartAt (closedSmoothModelWithCorners n) x).symm s
```

`Mathlib/Geometry/Manifold/Riemannian/Basic.lean` proves the one-point local
estimate `eventually_riemannianEDist_le_edist_extChartAt`.  The theorem above
requires the analogous pairwise estimate on a compact coordinate neighborhood,
obtained by pushing coordinate line segments through `(extChartAt I x).symm`
and bounding their `pathELength` using
`eventually_enorm_mfderivWithin_symm_extChartAt_lt`.
-/

noncomputable section

open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
open MeasureTheory

universe u v

namespace Poincare

/--
A Lipschitz image of a set with finite Hausdorff `d`-measure again has finite
Hausdorff `d`-measure.
-/
theorem hausdorffMeasure_image_lt_top_of_lipschitzOnWith
    {X : Type u} {Y : Type v}
    [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y]
    {K : ℝ≥0} {f : X → Y} {s : Set X} {d : ℝ}
    (hd : 0 ≤ d) (hLip : LipschitzOnWith K f s)
    (hs : (μH[d] : Measure X) s < (⊤ : ℝ≥0∞)) :
    (μH[d] : Measure Y) (f '' s) < (⊤ : ℝ≥0∞) := by
  refine lt_of_le_of_lt (hLip.hausdorffMeasure_image_le hd) ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top) hs

/--
Compact subsets of the closed smooth model space have finite `n`-dimensional
Hausdorff measure.
-/
theorem closedSmoothModel_hausdorffMeasure_lt_top {n : ℕ}
    {s : Set (ClosedSmoothModel n)} (hs : IsCompact s) :
    letI : MeasurableSpace (ClosedSmoothModel n) := borel (ClosedSmoothModel n)
    letI : BorelSpace (ClosedSmoothModel n) := ⟨rfl⟩
    (μH[(n : ℝ)] : Measure (ClosedSmoothModel n)) s < (⊤ : ℝ≥0∞) := by
  letI : MeasurableSpace (ClosedSmoothModel n) := borel (ClosedSmoothModel n)
  haveI : BorelSpace (ClosedSmoothModel n) := ⟨rfl⟩
  have hdim : (Module.finrank ℝ (ClosedSmoothModel n) : ℝ) = n := by
    simp [ClosedSmoothModel, finrank_euclideanSpace]
  simpa [hdim] using
    (hs.measure_lt_top (μ := (μH[(Module.finrank ℝ (ClosedSmoothModel n) : ℝ)] :
      Measure (ClosedSmoothModel n))))

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/--
Local finiteness of the induced Hausdorff measure implies finiteness on a
compact closed manifold.
-/
theorem volumeMeasure_isFiniteMeasure_of_forall_finiteAt_nhds
    (g : ClosedSmoothRiemannianMetric n M)
    (hlocal :
      letI : MetricSpace M := g.toMetricSpace
      ∀ x : M, (μH[(n : ℝ)] : Measure M).FiniteAtFilter (𝓝 x)) :
    IsFiniteMeasure (volumeMeasure g) := by
  letI : MetricSpace M := g.toMetricSpace
  have hlocal' : ∀ x : M, (μH[(n : ℝ)] : Measure M).FiniteAtFilter (𝓝 x) := hlocal
  haveI : IsLocallyFiniteMeasure (μH[(n : ℝ)] : Measure M) := ⟨hlocal'⟩
  haveI : IsFiniteMeasureOnCompacts (μH[(n : ℝ)] : Measure M) := inferInstance
  haveI : IsFiniteMeasure (μH[(n : ℝ)] : Measure M) := CompactSpace.isFiniteMeasure
  simpa [volumeMeasure]

/--
A compact coordinate set whose inverse chart image is a neighborhood and whose
inverse chart is Lipschitz gives a finite neighborhood for `volumeMeasure`.
-/
theorem volumeMeasure_finiteAt_nhds_of_compact_lipschitz_chart_image
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    {s : Set (ClosedSmoothModel n)} (hs : IsCompact s)
    (hsx : (extChartAt (closedSmoothModelWithCorners n) x).symm '' s ∈ 𝓝 x)
    {K : ℝ≥0}
    (hLip :
      letI : MetricSpace M := g.toMetricSpace
      LipschitzOnWith K (extChartAt (closedSmoothModelWithCorners n) x).symm s) :
    (volumeMeasure g).FiniteAtFilter (𝓝 x) := by
  letI : MetricSpace M := g.toMetricSpace
  letI : MeasurableSpace (ClosedSmoothModel n) := borel (ClosedSmoothModel n)
  haveI : BorelSpace (ClosedSmoothModel n) := ⟨rfl⟩
  have hfinite_s :
      (μH[(n : ℝ)] : Measure (ClosedSmoothModel n)) s < (⊤ : ℝ≥0∞) :=
    closedSmoothModel_hausdorffMeasure_lt_top hs
  have hfinite_image :
      (μH[(n : ℝ)] : Measure M)
          ((extChartAt (closedSmoothModelWithCorners n) x).symm '' s) <
        (⊤ : ℝ≥0∞) :=
    hausdorffMeasure_image_lt_top_of_lipschitzOnWith (by positivity) hLip hfinite_s
  exact ⟨_, hsx, by simpa [volumeMeasure] using hfinite_image⟩

/--
The final finiteness theorem reduces to the single missing local chart
comparison stated in the module docstring.
-/
theorem volumeMeasure_isFiniteMeasure_of_compact_lipschitz_chart_images
    (g : ClosedSmoothRiemannianMetric n M)
    (hchart : ∀ x : M,
      ∃ s : Set (ClosedSmoothModel n),
        IsCompact s ∧
        (extChartAt (closedSmoothModelWithCorners n) x).symm '' s ∈ 𝓝 x ∧
        ∃ K : ℝ≥0,
          letI : MetricSpace M := g.toMetricSpace
          LipschitzOnWith K (extChartAt (closedSmoothModelWithCorners n) x).symm s) :
    IsFiniteMeasure (volumeMeasure g) := by
  apply volumeMeasure_isFiniteMeasure_of_forall_finiteAt_nhds g
  intro x
  rcases hchart x with ⟨s, hs_compact, hs_nhds, K, hK⟩
  exact volumeMeasure_finiteAt_nhds_of_compact_lipschitz_chart_image
    g x hs_compact hs_nhds hK

end Poincare
