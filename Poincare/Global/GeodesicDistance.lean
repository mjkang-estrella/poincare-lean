import Poincare.Global.GaussLemmaRadial

/-!
# Riemannian distance and local geodesic-distance boundary

This module records the non-geodesic-specific path-length bridge needed for
the local distance formula: once the metric induced by `g` is installed,
Mathlib's Riemannian extended distance is exactly the ambient `edist`, and
every `C¹` path gives an upper bound by its `pathELength`.

The remaining local geodesic-distance step is to instantiate this bridge with
the radial exponential curve and compute that curve's `pathELength` from the
constant-speed Gauss lemma data.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n

/--
After installing the Riemannian emetric induced by `g`, Mathlib's
path-infimum Riemannian distance is definitionally the ambient extended
distance.
-/
theorem induced_edist_eq_riemannianEDist
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    letI : EMetricSpace M := g.toEMetricSpace
    edist x y = Manifold.riemannianEDist I x y := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  haveI : IsRiemannianManifold I M := g.toIsRiemannianManifold
  exact IsRiemannianManifold.out x y

/--
Any `C¹` path bounds the induced Riemannian extended distance by its
`pathELength`.  This is the project-context specialization of
`Manifold.riemannianEDist_le_pathELength`.
-/
theorem induced_edist_le_pathELength
    (g : ClosedSmoothRiemannianMetric n M) {x y : M} {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    letI : EMetricSpace M := g.toEMetricSpace
    edist x y ≤ Manifold.pathELength I γ a b := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  haveI : IsRiemannianManifold I M := g.toIsRiemannianManifold
  rw [induced_edist_eq_riemannianEDist (g := g) x y]
  exact Manifold.riemannianEDist_le_pathELength hγ ha hb hab

/--
Real-valued form of `induced_edist_le_pathELength`: if the `pathELength` of a
`C¹` path is bounded by `L`, then the ordinary metric distance induced by `g`
is bounded by `L`.
-/
theorem induced_dist_le_of_pathELength_le_ofReal
    [ConnectedSpace M] (g : ClosedSmoothRiemannianMetric n M)
    {x y : M} {γ : ℝ → M} {a b L : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) (hL : 0 ≤ L)
    (hLen :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      Manifold.pathELength I γ a b ≤ ENNReal.ofReal L) :
    letI : MetricSpace M := g.toMetricSpace
    dist x y ≤ L := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  have hEd : edist x y ≤ ENNReal.ofReal L :=
    (induced_edist_le_pathELength (g := g) hγ ha hb hab).trans hLen
  exact (edist_le_ofReal hL).mp hEd

end GeodesicTransport
end Poincare
