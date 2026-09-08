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

/-- Short terminal paths identify the total rooted-endpoint map on an open source neighborhood. -/
theorem development_eqOn_terminal_neighborhood [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk) (x : M),
  ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ (terminalGerm R x).source ∧
    EqOn (development R) (terminalGerm R x) W := by
  intro S sk R x
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨W, hW, hxW, hpaths⟩ := CartanSuppliedTerminalTransport.exists_short_paths S x
  refine ⟨W ∩ (terminalGerm R x).source,
    hW.inter (terminalGerm R x).open_source,
    ⟨hxW, (terminal_anchor_laws R x).1⟩, inter_subset_right, ?_⟩
  intro z hz
  obtain ⟨q, hq⟩ := hpaths z hz.1
  let s := terminalState R x
  have hs : s.anchor = x := endpoint_anchor S sk.root (sk.path x) (R.realization x)
  obtain ⟨T, _hT⟩ := exists_realization S s (q.cast hs rfl)
  obtain ⟨C, _hC⟩ := exists_realization S sk.root ((sk.path x).trans q)
  let a := fallback S.cover s
  have hv : S.cover.Valid a s :=
    ⟨Classical.choose_spec (S.cover.source.covers s.anchor),
      Classical.choose_spec (S.cover.target.covers s.target)⟩
  have hstep : S.mesh ≤ S.cover.step := by
    have := (four_mul_mesh_le S).1
    have := mesh_pos S
    linarith
  have hzstep : dist z s.anchor < S.cover.step := by
    rw [hs]
    have hzend : dist z x < S.mesh := by simpa only [Path.target] using hq 1
    exact hzend.trans_le hstep
  obtain ⟨d⟩ := (S.cover.h1 a.1 a.2 s.anchor
    (interior_subset (S.cover.source.core_subset a.1 hv.1)) s.target
    (interior_subset (S.cover.target.core_subset a.2 hv.2)) s.alignment z hzstep).2.2.2
  have hshort := CartanSuppliedTerminalTransport.short_path_endpoint S s
    (q.cast hs rfl) T (by simpa only [Path.cast_coe, hs] using hq) d
  have htrans := CartanSuppliedTerminalTransport.endpoint_trans S sk.root
    (sk.path x) q (R.realization x) hs T C
  have hroot := CartanSuppliedHomotopyEndpoints.endpoint_eq S sk.root
    (sk.path z) ((sk.path x).trans q) (R.realization z) C
  exact congrArg CartanChain.ChainState.target (hroot.trans (htrans.trans hshort))

/-- The verified terminal neighborhoods form a compatible restricted atlas. -/
theorem exists_restrictedAtlas [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk),
  ∃ A : RestrictedAtlas M, A.germ = terminalGerm R ∧ A.diagonal = development R := by
  intro S sk R
  choose W hW hxW hsource heq using development_eqOn_terminal_neighborhood S sk R
  let A : RestrictedAtlas M := {
    germ := terminalGerm R
    domain := W
    isOpen_domain := hW
    anchor_mem_domain := hxW
    domain_subset_source := hsource
    compatible := fun x y z hz => (heq x hz.1).symm.trans (heq y hz.2) }
  refine ⟨A, rfl, ?_⟩
  funext x
  exact (heq x (hxW x)).symm

omit inst [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Restricting each supplied germ to its atlas domain realizes the diagonal locally. -/
theorem isLocalHomeomorph_diagonal : ∀ A : RestrictedAtlas M,
    IsLocalHomeomorph A.diagonal := by
  intro A
  apply IsLocalHomeomorph.mk
  intro x
  let e := (A.germ x).restrOpen (A.domain x) (A.isOpen_domain x)
  refine ⟨e, ?_, ?_⟩
  · change x ∈ (A.germ x).source ∩ A.domain x
    exact ⟨A.domain_subset_source x (A.anchor_mem_domain x), A.anchor_mem_domain x⟩
  · intro z hz
    change z ∈ (A.germ x).source ∩ A.domain x at hz
    change A.germ z z = A.germ x z
    exact A.compatible z x ⟨A.anchor_mem_domain z, hz.2⟩

/-- The total map of rooted supplied endpoints is a local homeomorphism. -/
theorem isLocalHomeomorph_development [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk), IsLocalHomeomorph (development R) := by
  intro S sk R
  obtain ⟨A, _hgerm, hdiagonal⟩ := exists_restrictedAtlas S sk R
  rw [← hdiagonal]
  exact isLocalHomeomorph_diagonal A

end CartanSuppliedRestrictedDevelopment
end Poincare
