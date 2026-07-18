import Poincare.Global.HausdorffInverseChartLocalPathLengthComparison
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Short-path confinement for the Riemannian length metric

Local tensor comparison controls a curve only while it remains in the
comparison neighborhood.  This file supplies the complementary metric fact:
every neighborhood of a starting point contains every sufficiently short
`C¹` path starting there.

The proof has two layers.  First, every point on a path is at Riemannian
extended distance at most the length of the corresponding prefix, hence at
most the total path length.  Second, Mathlib's Riemannian metric construction
proves that a sufficiently small intrinsic-distance sublevel is contained in
any prescribed neighborhood.  Combining them gives a single positive length
threshold, uniform over all paths.
-/

noncomputable section

open Bundle Filter MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n

/-- Every point on a `C¹` path is at Riemannian extended distance from its
initial point at most the total length of the path.  In particular, a path
shorter than `c` is contained in the intrinsic `c`-sublevel. -/
theorem mapsTo_riemannianEDist_sublevel_of_pathELength_lt
    (g : ClosedSmoothRiemannianMetric n M)
    {x : M} {c : ℝ≥0∞} {a b : ℝ} {γ : ℝ → M}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (hγa : γ a = x) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    Manifold.pathELength I γ a b < c →
    MapsTo γ (Icc a b)
      {y | Manifold.riemannianEDist I x y < c} := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  intro hlen
  intro t ht
  have hγat := hγ.mono (Icc_subset_Icc le_rfl ht.2)
  have hprefixDist :
      Manifold.riemannianEDist I x (γ t) ≤
        Manifold.pathELength I γ a t :=
    Manifold.riemannianEDist_le_pathELength
      hγat hγa rfl ht.1
  have hprefixLength :
      Manifold.pathELength I γ a t ≤
        Manifold.pathELength I γ a b :=
    Manifold.pathELength_mono le_rfl ht.2
  exact (hprefixDist.trans hprefixLength).trans_lt hlen

/-- Every neighborhood of `x` has a positive, path-independent confinement
threshold: each `C¹` path beginning at `x` with smaller total length remains
in that neighborhood for its whole parameter interval. -/
theorem exists_pathELength_threshold_mapsTo_nhds
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ c > (0 : ℝ≥0∞), ∀ {a b : ℝ} {γ : ℝ → M},
      a ≤ b →
      ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b) →
      γ a = x →
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      Manifold.pathELength I γ a b < c →
        MapsTo γ (Icc a b) s := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  rcases setOf_riemannianEDist_lt_subset_nhds' I hs with
    ⟨c, hc, hsub⟩
  refine ⟨c, hc, ?_⟩
  intro a b γ hab hγ hγa hlen
  have hmap := mapsTo_riemannianEDist_sublevel_of_pathELength_lt
    (g := g) hab hγ hγa hlen
  intro t ht
  exact hsub (hmap ht)

end Poincare
