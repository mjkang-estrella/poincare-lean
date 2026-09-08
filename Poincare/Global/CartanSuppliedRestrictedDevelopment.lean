import Poincare.Global.CartanSuppliedHomotopyEndpoints
import Poincare.Global.CartanSuppliedTerminalTransport
import Poincare.Global.CartanRestrictedOverlapCompatibility

/-!
# Restricted development from supplied rooted endpoints

Short terminal paths identify the endpoint map with its selected supplied germ.
The resulting restricted domains give a compatible atlas and a local homeomorphism.
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

namespace CartanSuppliedRestrictedDevelopment
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

structure RestrictedAtlas (M : Type u) [TopologicalSpace M] where
  germ : M → OpenPartialHomeomorph M RoundSphere3
  domain : M → Set M
  isOpen_domain : ∀ x, IsOpen (domain x)
  anchor_mem_domain : ∀ x, x ∈ domain x
  domain_subset_source : ∀ x, domain x ⊆ (germ x).source
  compatible : ∀ x y, EqOn (germ x) (germ y) (domain x ∩ domain y)

def RestrictedAtlas.diagonal (A : RestrictedAtlas M) : M → RoundSphere3 :=
  fun x => A.germ x x

def terminalState {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) (x : M) : CartanChain.ChainState g :=
  (R.realization x).endpoint

def terminalGerm {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) (x : M) : OpenPartialHomeomorph M RoundSphere3 :=
  germ (S.cover.interp (fallback S.cover (terminalState R x))) (terminalState R x)

def development {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) : M → RoundSphere3 :=
  fun x => (terminalState R x).target

/-- The fallback germ contains its terminal anchor and takes the endpoint value there. -/
theorem terminal_anchor_laws {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) (x : M) :
    x ∈ (terminalGerm R x).source ∧ terminalGerm R x x = development R x := by
  let s := terminalState R x
  let a := fallback S.cover s
  have hv : S.cover.Valid a s :=
    ⟨Classical.choose_spec (S.cover.source.covers s.anchor),
      Classical.choose_spec (S.cover.target.covers s.target)⟩
  have hx := S.cover.source.buffer_subset a.1
    (interior_subset (S.cover.source.core_subset a.1 hv.1))
  have hp := S.cover.target.buffer_subset a.2
    (interior_subset (S.cover.target.core_subset a.2 hv.2))
  have h := anchor_laws (S.cover.interp a) s hx hp
  have hs : s.anchor = x := endpoint_anchor S sk.root (sk.path x) (R.realization x)
  simpa only [hs] using h

end CartanSuppliedRestrictedDevelopment
end Poincare
