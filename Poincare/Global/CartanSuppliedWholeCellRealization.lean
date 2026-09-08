import Poincare.Global.CartanSuppliedPatchPolicy
import Poincare.Global.CartanAtlasRootedPathSkeleton
import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition

/-!
# Supplied chains on strict whole-cell subdivisions

Parameter cells are chosen geometrically before selecting any supplied data.
Realizations retain their actual preferred labels and reached differential chain.
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

namespace CartanSuppliedWholeCellRealization
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
structure Subdivision {x y : M} (p : Path x y) (r : ℝ) where
  time : ℕ → unitInterval
  terminal : ℕ
  zero : time 0 = 0
  mono : Monotone time
  strict : ∀ n < terminal, time n < time (n + 1)
  tail : ∀ n ≥ terminal, time n = 1
  wholeCell : letI : MetricSpace M := g.toMetricSpace
    ∀ n (a b : unitInterval), a ∈ Icc (time n) (time (n + 1)) →
      b ∈ Icc (time n) (time (n + 1)) → dist (p a) (p b) < r

structure Realization (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) where
  subdivision : Subdivision (g := g) p S.mesh
  preferred : ℕ → S.cover.Label
  chain : ReachableChain (policy S.cover preferred)
    (fun n => p (subdivision.time n)) initial

def Realization.endpoint {S : System g} {initial : CartanChain.ChainState g}
    {y : M} {p : Path initial.anchor y} (R : Realization S initial p) :
    CartanChain.ChainState g := R.chain.state R.subdivision.terminal

structure RootedRealization (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g) where
  realization : ∀ x : M, Realization S skeleton.root (skeleton.path x)

theorem endpoint_anchor : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R : Realization S initial p),
    R.endpoint.anchor = y := by
  intro S initial y p R
  have hinitial : initial.anchor = p (R.subdivision.time 0) := by
    simp [R.subdivision.zero]
  have h := state_anchor_eq_node _ _ initial R.chain hinitial R.subdivision.terminal
  simpa only [Realization.endpoint, R.subdivision.tail _ le_rfl, Path.target] using h

end CartanSuppliedWholeCellRealization
end Poincare
