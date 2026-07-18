import Poincare.Global.CartanOverlapCompatibility
import Poincare.Global.RigidityComplete
import Mathlib.Topology.Connected.Clopen

/-!
# Connected continuation for Cartan overlap compatibility

The remaining Cartan globalization input is an equality of two locally defined
Cartan maps on their full common source.  This module separates the global
continuation part of that assertion from its genuinely local Riemannian part.

For two open partial homeomorphisms into a Hausdorff space, their equality
locus on a common source is closed.  If local rigidity makes that equality
locus open, preconnectedness and one equality seed force equality on the whole
overlap.  The final theorem specializes this clopen continuation argument to
the all-anchor re-centering payload used by `CartanOverlapCompatibility`.

Thus it is no longer necessary to prove the charted re-centering formula at
every overlap point directly.  It is enough to prove:

* preconnectedness of each nonempty common normal-coordinate source;
* one equality seed in it; and
* the local value-and-differential uniqueness step near any equality point.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanOverlapContinuation

universe u v

/--
Clopen continuation on an arbitrary preconnected set.

This is the topological core of local-isometry determinacy.  It is stated for
ordinary functions so it can also be applied separately on every connected
component of an overlap.
-/
theorem eqOn_of_preconnected_of_continuousOn_of_local_rigidity
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {F G : X → Y} {S : Set X}
    (hpre : IsPreconnected S) (hF : ContinuousOn F S)
    (hG : ContinuousOn G S)
    (hseed : ∃ x ∈ S, F x = G x)
    (hlocal :
      ∀ x ∈ S, F x = G x →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ EqOn F G (V ∩ S)) :
    EqOn F G S := by
  have hF' : Continuous (fun x : S => F x) :=
    continuousOn_iff_continuous_restrict.mp hF
  have hG' : Continuous (fun x : S => G x) :=
    continuousOn_iff_continuous_restrict.mp hG
  let A : Set S := {x | F x = G x}
  have hA_closed : IsClosed A := by
    simpa [A] using isClosed_eq hF' hG'
  have hA_open : IsOpen A := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    rcases hlocal x x.property (by simpa [A] using hx) with
      ⟨V, hV_open, hxV, hVG⟩
    refine ⟨Subtype.val ⁻¹' V, ?_, hV_open.preimage continuous_subtype_val, hxV⟩
    intro y hy
    have hyEq : F y = G y := hVG ⟨hy, y.property⟩
    simpa [A] using hyEq
  letI : PreconnectedSpace S :=
    isPreconnected_iff_preconnectedSpace.mp hpre
  rcases hseed with ⟨x, hxS, hxEq⟩
  have hA_nonempty : A.Nonempty := by
    exact ⟨⟨x, hxS⟩, by simpa [A] using hxEq⟩
  have hA_univ : A = Set.univ :=
    (show IsClopen A from ⟨hA_closed, hA_open⟩).eq_univ hA_nonempty
  intro y hy
  have hyA : (⟨y, hy⟩ : S) ∈ A := by
    rw [hA_univ]
    exact Set.mem_univ _
  simpa [A] using hyA

/--
Componentwise continuation removes any connectedness requirement on the whole
overlap.  A local-rigidity equality propagates through each connected
component, so one equality seed in every component suffices.
-/
theorem eqOn_of_componentwise_seed_of_continuousOn_of_local_rigidity
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {F G : X → Y} {S : Set X}
    (hF : ContinuousOn F S) (hG : ContinuousOn G S)
    (hseed : ∀ x ∈ S,
      ∃ z ∈ connectedComponentIn S x, F z = G z)
    (hlocal :
      ∀ x ∈ S, F x = G x →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ EqOn F G (V ∩ S)) :
    EqOn F G S := by
  intro x hx
  let C : Set X := connectedComponentIn S x
  have hC_sub : C ⊆ S := by
    simpa [C] using connectedComponentIn_subset S x
  have hFC : ContinuousOn F C := hF.mono hC_sub
  have hGC : ContinuousOn G C := hG.mono hC_sub
  rcases hseed x hx with ⟨z, hzC, hzEq⟩
  have hEqC : EqOn F G C :=
    eqOn_of_preconnected_of_continuousOn_of_local_rigidity
      (by simpa [C] using
        (isPreconnected_connectedComponentIn :
          IsPreconnected (connectedComponentIn S x)))
      hFC hGC ⟨z, by simpa [C] using hzC, hzEq⟩ (by
        intro y hyC hyEq
        rcases hlocal y (hC_sub hyC) hyEq with ⟨V, hV, hyV, hVS⟩
        refine ⟨V, hV, hyV, ?_⟩
        intro w hw
        exact hVS ⟨hw.1, hC_sub hw.2⟩)
  exact hEqC (by simpa [C] using mem_connectedComponentIn hx)

/--
Connected continuation for two open partial homeomorphisms.

Continuity on the two sources makes the equality locus closed in the subtype
`F.source ∩ G.source`.  The local-rigidity hypothesis makes it open.  A seed
then forces the equality locus to be the whole preconnected overlap.
-/
theorem openPartialHomeomorph_eqOn_of_preconnected_overlap_of_local_rigidity
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (F G : OpenPartialHomeomorph X Y)
    (hpre : IsPreconnected (F.source ∩ G.source))
    (hseed : (F.source ∩ G.source).Nonempty →
      ∃ x ∈ F.source ∩ G.source, F x = G x)
    (hlocal :
      ∀ x ∈ F.source ∩ G.source, F x = G x →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
          EqOn F G (V ∩ (F.source ∩ G.source))) :
    EqOn F G (F.source ∩ G.source) := by
  let S : Set X := F.source ∩ G.source
  by_cases hS : S.Nonempty
  · have hF : ContinuousOn F S :=
      F.continuousOn.mono (by
        intro x hx
        exact hx.1)
    have hG : ContinuousOn G S :=
      G.continuousOn.mono (by
        intro x hx
        exact hx.2)
    have hF' : Continuous (fun x : S => F x) :=
      continuousOn_iff_continuous_restrict.mp hF
    have hG' : Continuous (fun x : S => G x) :=
      continuousOn_iff_continuous_restrict.mp hG
    let A : Set S := {x | F x = G x}
    have hA_closed : IsClosed A := by
      simpa [A] using isClosed_eq hF' hG'
    have hA_open : IsOpen A := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      rcases hlocal x x.property (by simpa [A] using hx) with
        ⟨V, hV_open, hxV, hVG⟩
      refine ⟨Subtype.val ⁻¹' V, ?_, hV_open.preimage continuous_subtype_val, hxV⟩
      intro y hy
      have hyV : (y : X) ∈ V := hy
      have hyEq : F y = G y := hVG ⟨hyV, y.property⟩
      simpa [A] using hyEq
    letI : PreconnectedSpace S :=
      isPreconnected_iff_preconnectedSpace.mp (by simpa [S] using hpre)
    rcases hseed (by simpa [S] using hS) with ⟨x, hxS, hxEq⟩
    have hA_nonempty : A.Nonempty := by
      refine ⟨⟨x, by simpa [S] using hxS⟩, ?_⟩
      simpa [A] using hxEq
    have hA_univ : A = Set.univ :=
      (show IsClopen A from ⟨hA_closed, hA_open⟩).eq_univ hA_nonempty
    intro y hy
    have hyA : (⟨y, by simpa [S] using hy⟩ : S) ∈ A := by
      rw [hA_univ]
      exact Set.mem_univ _
    simpa [A] using hyA
  · intro x hx
    exact (hS ⟨x, by simpa [S] using hx⟩).elim

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
The connected-overlap/local-rigidity replacement for pointwise all-anchor
Cartan naturality.

The final clause is precisely the local uniqueness statement expected from
the classical fact that a local isometry is determined by its value and
differential.  Unlike the original all-point identity, it only asks for that
fact in a neighborhood of a point where the two germs already agree.
-/
def UnitCurvatureConnectedOverlapLocalRigidity3
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ (p : M → RoundSphere3)
        (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
          ∀ x y : M,
            let Fx := CartanMap.openPartialHomeomorph g x (p x) (L x)
            let Fy := CartanMap.openPartialHomeomorph g y (p y) (L y)
            IsPreconnected (Fx.source ∩ Fy.source) ∧
              ((Fx.source ∩ Fy.source).Nonempty →
                ∃ z ∈ Fx.source ∩ Fy.source, Fx z = Fy z) ∧
              (∀ z ∈ Fx.source ∩ Fy.source, Fx z = Fy z →
                ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
                  EqOn Fx Fy (V ∩ (Fx.source ∩ Fy.source)))

/--
The componentwise form of the Cartan overlap continuation payload.

This form does not assume that an intersection of two normal-coordinate
sources is preconnected.  Instead it asks for one equality seed in each
connected component, which is the exact hypothesis needed by continuation.
-/
def UnitCurvatureComponentwiseOverlapLocalRigidity3
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ (p : M → RoundSphere3)
        (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
          ∀ x y : M,
            let Fx := CartanMap.openPartialHomeomorph g x (p x) (L x)
            let Fy := CartanMap.openPartialHomeomorph g y (p y) (L y)
            (∀ z ∈ Fx.source ∩ Fy.source,
              ∃ w ∈ connectedComponentIn (Fx.source ∩ Fy.source) z,
                Fx w = Fy w) ∧
              (∀ z ∈ Fx.source ∩ Fy.source, Fx z = Fy z →
                ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
                  EqOn Fx Fy (V ∩ (Fx.source ∩ Fy.source)))

/--
Connected overlaps, one seed, and local Cartan rigidity imply the full
all-anchor charted re-centering identity.

This is the direct reduction to the remaining local-isometry uniqueness
theorem: the clopen continuation argument supplies every other point of every
overlap automatically.
-/
theorem chartedRecenterNaturality_of_connectedOverlapLocalRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hlocal : UnitCurvatureConnectedOverlapLocalRigidity3 (M := M)) :
    CartanOverlapCompatibility.UnitCurvatureChartedRecenterNaturality3
      (M := M) := by
  intro g hcurv
  rcases hlocal g hcurv with ⟨p, L, hL⟩
  refine ⟨p, L, ?_⟩
  intro x y z hz
  let Fx := CartanMap.openPartialHomeomorph g x (p x) (L x)
  let Fy := CartanMap.openPartialHomeomorph g y (p y) (L y)
  rcases hL x y with ⟨hpre, hseed, hrigid⟩
  have hEq : EqOn Fx Fy (Fx.source ∩ Fy.source) :=
    openPartialHomeomorph_eqOn_of_preconnected_overlap_of_local_rigidity
      Fx Fy hpre hseed hrigid
  change Fx z = Fy z
  exact hEq hz

/--
Componentwise seeds and local Cartan rigidity imply the full all-anchor
charted re-centering identity, without a connected-overlap assumption.
-/
theorem chartedRecenterNaturality_of_componentwiseOverlapLocalRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hlocal : UnitCurvatureComponentwiseOverlapLocalRigidity3 (M := M)) :
    CartanOverlapCompatibility.UnitCurvatureChartedRecenterNaturality3
      (M := M) := by
  intro g hcurv
  rcases hlocal g hcurv with ⟨p, L, hL⟩
  refine ⟨p, L, ?_⟩
  intro x y z hz
  let Fx := CartanMap.openPartialHomeomorph g x (p x) (L x)
  let Fy := CartanMap.openPartialHomeomorph g y (p y) (L y)
  rcases hL x y with ⟨hseed, hrigid⟩
  have hF : ContinuousOn Fx (Fx.source ∩ Fy.source) :=
    Fx.continuousOn.mono inter_subset_left
  have hG : ContinuousOn Fy (Fx.source ∩ Fy.source) :=
    Fy.continuousOn.mono inter_subset_right
  have hEq : EqOn Fx Fy (Fx.source ∩ Fy.source) :=
    eqOn_of_componentwise_seed_of_continuousOn_of_local_rigidity
      hF hG hseed hrigid
  change Fx z = Fy z
  exact hEq hz

/--
The same connected-continuation payload therefore supplies the compatible
Cartan atlas consumed by unit-curvature recognition.
-/
theorem compatibleCartanAtlas_of_connectedOverlapLocalRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hlocal : UnitCurvatureConnectedOverlapLocalRigidity3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  CartanOverlapCompatibility.compatibleCartanAtlas_of_chartedRecenterNaturality
    (chartedRecenterNaturality_of_connectedOverlapLocalRigidity hlocal)

/-- The componentwise continuation payload also supplies the compatible atlas. -/
theorem compatibleCartanAtlas_of_componentwiseOverlapLocalRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hlocal : UnitCurvatureComponentwiseOverlapLocalRigidity3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  CartanOverlapCompatibility.compatibleCartanAtlas_of_chartedRecenterNaturality
    (chartedRecenterNaturality_of_componentwiseOverlapLocalRigidity hlocal)

end CartanOverlapContinuation
end Poincare
