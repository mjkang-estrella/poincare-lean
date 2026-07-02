import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic

/-!
# Standard Riemannian context
This module packages the project-level tier M1 context for a closed smooth
Riemannian `n`-manifold.  The intended downstream variable section is:
```lean
open scoped Manifold ContDiff Bundle
variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]
variable (g : Poincare.ClosedSmoothRiemannianMetric n M)
```
From the single metric variable `g`, use the definitions below as local
instances when a downstream statement needs Mathlib's bundle or distance
typeclasses.
-/
noncomputable section
open Bundle Bornology
open scoped Manifold ContDiff Bundle Topology ENNReal
universe u
namespace Poincare

/-- The model vector space for a boundaryless smooth `n`-manifold. -/
abbrev ClosedSmoothModel (n : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n)

/-- The model-with-corners used for boundaryless smooth `n`-manifolds. -/
abbrev closedSmoothModelWithCorners (n : ℕ) :
    ModelWithCorners ℝ (ClosedSmoothModel n) (ClosedSmoothModel n) :=
  𝓡 n

/--
A smooth Riemannian metric on the tangent bundle of a smooth `n`-manifold.

This is the single non-typeclass metric variable used by the project context.
All Mathlib bundle and distance typeclasses below are derived from this data.
-/
abbrev ClosedSmoothRiemannianMetric (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M] :=
  ContMDiffRiemannianMetric (closedSmoothModelWithCorners n) ∞ (ClosedSmoothModel n)
    (fun x : M => TangentSpace (closedSmoothModelWithCorners n) x)

namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- The tangent bundle family in the standard closed smooth context. -/
abbrev tangentBundle : M → Type _ :=
  fun x : M => TangentSpace (closedSmoothModelWithCorners n) x

/-- Register the inner products supplied by a smooth tangent-bundle metric. -/
@[reducible] def toRiemannianBundle (g : ClosedSmoothRiemannianMetric n M) :
    RiemannianBundle (tangentBundle (n := n) (M := M)) :=
  ⟨g.toRiemannianMetric⟩

/-- A smooth metric gives Mathlib's smooth Riemannian-bundle typeclass. -/
@[reducible] def toIsContMDiffRiemannianBundle (g : ClosedSmoothRiemannianMetric n M) :
    letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
    IsContMDiffRiemannianBundle (closedSmoothModelWithCorners n) ∞
      (ClosedSmoothModel n) (tangentBundle (n := n) (M := M)) := by
  letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
  exact ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩

/-- A smooth metric gives Mathlib's continuous Riemannian-bundle typeclass. -/
@[reducible] def toIsContinuousRiemannianBundle (g : ClosedSmoothRiemannianMetric n M) :
    letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
    IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (tangentBundle (n := n) (M := M)) := by
  letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
  exact ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩

/-- The pseudoemetric space induced by the Riemannian path-length construction. -/
@[reducible] def toPseudoEMetricSpace [T2Space M] [CompactSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    PseudoEMetricSpace M := by
  letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (tangentBundle (n := n) (M := M)) := g.toIsContinuousRiemannianBundle
  exact PseudoEMetricSpace.ofRiemannianMetric (closedSmoothModelWithCorners n) M

/-- The emetric space induced by the Riemannian path-length construction. -/
@[reducible] def toEMetricSpace [T2Space M] [CompactSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    EMetricSpace M := by
  letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (tangentBundle (n := n) (M := M)) := g.toIsContinuousRiemannianBundle
  exact EMetricSpace.ofRiemannianMetric (closedSmoothModelWithCorners n) M

/-- With the induced emetric, Mathlib's Riemannian-manifold predicate is definitional. -/
@[reducible] def toIsRiemannianManifold [T2Space M] [CompactSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
    letI : EMetricSpace M := g.toEMetricSpace
    IsRiemannianManifold (closedSmoothModelWithCorners n) M := by
  letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  exact ⟨fun _ _ => rfl⟩

/-- The scalar-product section of a smooth tangent-bundle metric is smooth. -/
theorem contMDiff_inner (g : ClosedSmoothRiemannianMetric n M) :
    ContMDiff (closedSmoothModelWithCorners n)
      ((closedSmoothModelWithCorners n).prod
        𝓘(ℝ, (ClosedSmoothModel n) →L[ℝ] (ClosedSmoothModel n) →L[ℝ] ℝ))
      ∞
      (fun x : M =>
        TotalSpace.mk' ((ClosedSmoothModel n) →L[ℝ] (ClosedSmoothModel n) →L[ℝ] ℝ)
          x (g.inner x)) :=
  g.contMDiff

/-- Symmetry of the metric tensor in tangent fibers. -/
theorem inner_symm (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v w : tangentBundle (n := n) (M := M) x) :
    g.inner x v w = g.inner x w v :=
  g.symm x v w

/-- Positivity of the metric tensor on nonzero tangent vectors. -/
theorem inner_pos (g : ClosedSmoothRiemannianMetric n M) (x : M)
    {v : tangentBundle (n := n) (M := M) x} (hv : v ≠ 0) :
    0 < g.inner x v v :=
  g.pos x v hv

/-- Nonnegativity of the metric tensor on the diagonal. -/
theorem inner_nonneg (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v : tangentBundle (n := n) (M := M) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.inner_pos x hv).le

/-- The Riemannian unit ball in each tangent fiber is von Neumann bounded. -/
theorem isVonNBounded_unitBall (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    IsVonNBounded ℝ {v : tangentBundle (n := n) (M := M) x | g.inner x v v < 1} :=
  g.isVonNBounded x

/-- After installing `g`, Mathlib's fiber inner product is the metric tensor. -/
theorem fiber_inner_eq (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v w : tangentBundle (n := n) (M := M) x) :
    letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
    inner ℝ v w = g.inner x v w := by
  rfl

/-- Specialization of `ContMDiff.inner_bundle` to tangent vector fields. -/
theorem contMDiff_fiber_inner (g : ClosedSmoothRiemannianMetric n M)
    {V W : ∀ x : M, tangentBundle (n := n) (M := M) x}
    (hV : ContMDiff (closedSmoothModelWithCorners n)
      ((closedSmoothModelWithCorners n).prod 𝓘(ℝ, ClosedSmoothModel n)) ∞
      (fun x : M => (V x : TotalSpace (ClosedSmoothModel n)
        (tangentBundle (n := n) (M := M)))))
    (hW : ContMDiff (closedSmoothModelWithCorners n)
      ((closedSmoothModelWithCorners n).prod 𝓘(ℝ, ClosedSmoothModel n)) ∞
      (fun x : M => (W x : TotalSpace (ClosedSmoothModel n)
        (tangentBundle (n := n) (M := M))))) :
    letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
    ContMDiff (closedSmoothModelWithCorners n) 𝓘(ℝ) ∞
      (fun x : M => inner ℝ (V x) (W x)) := by
  letI : RiemannianBundle (tangentBundle (n := n) (M := M)) := g.toRiemannianBundle
  haveI : IsContMDiffRiemannianBundle (closedSmoothModelWithCorners n) ∞
      (ClosedSmoothModel n) (tangentBundle (n := n) (M := M)) :=
    g.toIsContMDiffRiemannianBundle
  exact ContMDiff.inner_bundle hV hW

/-- In the connected induced emetric, every extended distance is finite. -/
theorem induced_edist_ne_top [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) :
    letI : EMetricSpace M := g.toEMetricSpace
    edist x y ≠ ⊤ := by
  letI : EMetricSpace M := g.toEMetricSpace
  have hclopen : IsClopen (Metric.eball x (⊤ : ℝ≥0∞)) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hnonempty : (Metric.eball x (⊤ : ℝ≥0∞)).Nonempty :=
    ⟨x, Metric.mem_eball_self (by simp)⟩
  have hy : y ∈ Metric.eball x (⊤ : ℝ≥0∞) := by
    simp [hclopen.eq_univ hnonempty]
  have hfinite : edist x y < ⊤ := by
    simpa [edist_comm] using hy
  exact hfinite.ne

/-- The ordinary metric space induced by the connected Riemannian emetric. -/
@[reducible] def toMetricSpace [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    MetricSpace M := by
  letI : EMetricSpace M := g.toEMetricSpace
  exact EMetricSpace.toMetricSpace fun x y => g.induced_edist_ne_top x y

end ClosedSmoothRiemannianMetric

end Poincare
