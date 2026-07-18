import Poincare.Global.CartanAtlasRootedReachableEndpointTransport
import Poincare.Global.TangentAlignmentExists
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Automatic rooted path skeleton for Cartan continuation

A connected smooth manifold is locally path connected, hence path connected.
After choosing one source anchor, one round-sphere target, and the guaranteed
tangent alignment, every source point therefore has a path from the same
Cartan root.  This removes root-state and path-choice existence from the
rooted continuation boundary; only the finite realized sampling/chain data
remain geometric.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanAtlasRootedPathSkeleton

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanAtlasRootedReachableEndpointTransport
open DifferentialInducedSuccessor.Chain

/-- A fixed Cartan root together with paths from that root to every source
point. -/
structure RootedCartanPathSkeleton
    (g : ClosedSmoothRiemannianMetric 3 M) where
  root : CartanChain.ChainState g
  path : ∀ x : M, Path root.anchor x

/-- Any chosen source anchor extends to a Cartan root from which every point
is reachable by a path.  The target anchor and tangent alignment are supplied
by nonemptiness, while connected-manifold topology supplies the paths. -/
def rootedCartanPathSkeletonAt
    [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    RootedCartanPathSkeleton g := by
  letI : LocPathConnectedSpace M :=
    ChartedSpace.locPathConnectedSpace E M
  letI : PathConnectedSpace M :=
    PathConnectedSpace.of_locPathConnectedSpace
  let p₀ : RoundSphere3 := Classical.choice inferInstance
  let L₀ : CartanMap.TangentAlignment g x₀ p₀ :=
    Classical.choice (CartanMap.tangentAlignment_nonempty g x₀ p₀)
  let root : CartanChain.ChainState g :=
    { anchor := x₀
      target := p₀
      alignment := L₀ }
  exact
    { root := root
      path := fun x ↦ (PathConnectedSpace.joined x₀ x).somePath }

/-- On a nonempty connected smooth manifold, a rooted Cartan path skeleton
exists without any constant-curvature assumption. -/
theorem nonempty_rootedCartanPathSkeleton
    [Nonempty M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) :
    Nonempty (RootedCartanPathSkeleton g) :=
  ⟨rootedCartanPathSkeletonAt g (Classical.choice inferInstance)⟩

/-- The remaining realization data over an automatic rooted path skeleton:
finite terminal sampling and an actual differential-successor chain along
each selected path. -/
structure RootedPathChainRealization
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g) where
  nodeTime : M → ℕ → unitInterval
  nodeTime_zero : ∀ x : M, nodeTime x 0 = 0
  terminalIndex : M → ℕ
  nodeTime_terminal : ∀ x : M, nodeTime x (terminalIndex x) = 1
  chain : ∀ x : M,
    ReachableChain
      (fun n ↦ skeleton.path x (nodeTime x n)) skeleton.root

/-- Realized finite chain data over the automatic path skeleton is exactly
the rooted endpoint family consumed by the transport construction. -/
def RootedPathChainRealization.toEndpointFamily
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (realization : RootedPathChainRealization skeleton) :
    RootedPathContinuedEndpointFamily g where
  root := skeleton.root
  path := skeleton.path
  nodeTime := realization.nodeTime
  nodeTime_zero := realization.nodeTime_zero
  terminalIndex := realization.terminalIndex
  nodeTime_terminal := realization.nodeTime_terminal
  chain := realization.chain

end CartanAtlasRootedPathSkeleton
end Poincare
