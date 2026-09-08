import Poincare.Global.CartanSuppliedSubdivisionTransport

/-!
# Transport through supplied subdivision blocks

Open agreement at each inserted node identifies the full differential successor.
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
namespace CartanSuppliedTerminalTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

open CartanSuppliedSubdivisionTransport

/-- The path component of the positive mesh ball supplies short terminal paths. -/
theorem exists_short_paths : ∀ (S : System g) (x : M),
  ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
    ∀ z ∈ W, ∃ q : Path x z,
      letI : MetricSpace M := g.toMetricSpace
      ∀ t : unitInterval, dist (q t) x < S.mesh := by
  intro S x
  letI : MetricSpace M := g.toMetricSpace
  letI : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace E M
  refine ⟨pathComponentIn (ball x S.mesh) x, isOpen_ball.pathComponentIn x,
    mem_pathComponentIn_self (mem_ball_self (mesh_pos S)), ?_⟩
  intro z hz
  exact ⟨hz.somePath, hz.somePath_mem⟩

end CartanSuppliedTerminalTransport
end Poincare
