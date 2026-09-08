import Poincare.Global.CartanSuppliedSubdivisionTransport
import Poincare.Global.DifferentialSuccessorAdjacentContinuation

/-!
# Homotopy invariance of supplied endpoints

Closed grid cells control all their points before any supplied chain is chosen.
-/

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain
namespace CartanSuppliedHomotopyEndpoints
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization CartanSuppliedSubdivisionTransport

def GridSmall (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q) (t : ℕ → unitInterval) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m n (a b c d : unitInterval),
    a ∈ Icc (t m) (t (m + 1)) → b ∈ Icc (t m) (t (m + 1)) →
    c ∈ Icc (t n) (t (n + 1)) → d ∈ Icc (t n) (t (n + 1)) →
    dist (H (a, c)) (H (b, d)) < S.mesh

/-- Half-mesh balls on the compact homotopy image give pairwise closed-cell control. -/
theorem exists_grid : ∀ (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q),
  ∃ (t : ℕ → unitInterval) (k : ℕ), t 0 = 0 ∧ Monotone t ∧
    (∀ n ≥ k, t n = 1) ∧ GridSmall S H t := by
  intro S x y p q H
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨t, htzero, htmono, ⟨k, httail⟩, hcell⟩ :=
    DifferentialSuccessorAdjacentContinuation.exists_homotopy_metricBall_grid
      g H.toContinuousMap (fun z : unitInterval × unitInterval => H z)
      (fun _ => S.mesh / 2) (fun z => ⟨z, by simpa using half_pos (mesh_pos S)⟩)
  refine ⟨t, k, htzero, htmono, httail, ?_⟩
  intro m n a b c d ha hb hc hd
  obtain ⟨z, hz⟩ := hcell m n
  have h₁ := hz a ha c hc
  have h₂ := hz b hb d hd
  change dist (H (a, c)) (H z) < S.mesh / 2 at h₁
  change dist (H (b, d)) (H z) < S.mesh / 2 at h₂
  have := dist_triangle_right (H (a, c)) (H (b, d)) (H z)
  linarith

end CartanSuppliedHomotopyEndpoints
end Poincare
