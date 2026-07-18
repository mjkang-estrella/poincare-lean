import Poincare.Global.SphereTheorem
import Poincare.Global.CoveringSkeleton
import Poincare.Global.RoundSphereMetric
import Poincare.Global.CartanMap
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Global developing-map consumer for unit-curvature recognition

This module isolates the exact topological payload needed after the local
Cartan--Ambrose--Hicks construction has been continued to a total developing
map.  Compactness turns a local homeomorphism into a covering map.  When the
round three-sphere is supplied with its standard simple-connectivity instance,
the covering is a homeomorphism.  An alternative criterion using injectivity
does not need that instance.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

universe u

namespace Poincare
namespace UnitRecognitionNext

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/--
The remaining geometric globalization payload in developing-map form.

For every unit-constant-curvature metric, it asks only for a total local
homeomorphism to the round sphere.  In particular it does not ask the
construction to prove global injectivity, surjectivity, or directly package a
homeomorphism.
-/
def UnitCurvatureGlobalLocalDevelopment3 : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ F : M → RoundSphere3, IsLocalHomeomorph F

/--
Variant of the developing-map payload with global injectivity.  This criterion
is useful independently of an imported simple-connectivity theorem for the
literal `Metric.sphere` model.
-/
def UnitCurvatureInjectiveLocalDevelopment3 : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ F : M → RoundSphere3, IsLocalHomeomorph F ∧ Injective F

/--
The repository-specific Cartan globalization payload.

Instead of asking for any topological property of the total map, this asks for
one function assembled coherently from the already constructed normal Cartan
germ at every anchor.  Membership of the anchor in each germ source is already
proved by `CartanMap.anchor_mem_source`.
-/
def UnitCurvatureCoherentCartanGerms3 : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ F : M → RoundSphere3,
        ∀ x : M,
          ∃ (p : RoundSphere3) (L : CartanMap.TangentAlignment g x p),
            EqOn F (CartanMap.openPartialHomeomorph g x p L)
              (CartanMap.openPartialHomeomorph g x p L).source

/--
Pairwise-compatible Cartan atlas form of the globalization payload.

There is one anchored normal Cartan germ at every point and any two germs
agree on their common source.  This is the direct all-anchors analogue of the
`EqOn` compatibility staged by `CartanContinuation` for successive germs.
-/
def UnitCurvatureCompatibleCartanAtlas3 : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ (p : M → RoundSphere3)
        (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
          ∀ x y : M,
            EqOn
              (CartanMap.openPartialHomeomorph g x (p x) (L x))
              (CartanMap.openPartialHomeomorph g y (p y) (L y))
              ((CartanMap.openPartialHomeomorph g x (p x) (L x)).source ∩
                (CartanMap.openPartialHomeomorph g y (p y) (L y)).source)

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] in
/--
Pairwise overlap agreement glues the anchored Cartan atlas to a coherent total
map.  At a point `y`, define the map using the germ anchored at `y`; agreement
with the germ anchored at `x` follows from pairwise compatibility because `y`
belongs to its own germ source.
-/
theorem coherentCartanGerms_of_compatibleCartanAtlas
    (hAtlas : UnitCurvatureCompatibleCartanAtlas3 (M := M)) :
    UnitCurvatureCoherentCartanGerms3 (M := M) := by
  intro g hcurv
  rcases hAtlas g hcurv with ⟨p, L, hcompat⟩
  let F : M → RoundSphere3 := fun y ↦
    CartanMap.openPartialHomeomorph g y (p y) (L y) y
  have hF : ∀ x : M,
      EqOn F (CartanMap.openPartialHomeomorph g x (p x) (L x))
        (CartanMap.openPartialHomeomorph g x (p x) (L x)).source := by
    intro x y hy
    exact
      hcompat y x
        ⟨CartanMap.anchor_mem_source g y (p y) (L y), hy⟩
  exact ⟨F, fun x ↦ ⟨p x, L x, hF x⟩⟩

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] in
/--
Coherent Cartan germs automatically provide a global local developing map.
This consumes the exact `EqOn` output expected from continuation/gluing and
removes any separate continuity, openness, or local-invertibility proof.
-/
theorem globalLocalDevelopment_of_coherentCartanGerms
    (hCartan : UnitCurvatureCoherentCartanGerms3 (M := M)) :
    UnitCurvatureGlobalLocalDevelopment3 (M := M) := by
  intro g hcurv
  rcases hCartan g hcurv with ⟨F, hF⟩
  have hF_local : IsLocalHomeomorph F := by
    apply IsLocalHomeomorph.mk
    intro x
    rcases hF x with ⟨p, L, hEq⟩
    exact
      ⟨CartanMap.openPartialHomeomorph g x p L,
        CartanMap.anchor_mem_source g x p L, hEq⟩
  exact ⟨F, hF_local⟩

/--
A compact connected source cannot embed by a local homeomorphism into a proper
part of a connected Hausdorff target.  Thus injectivity is the only global map
property needed to obtain the bundled homeomorphism.
-/
theorem homeomorph_of_compact_injective_isLocalHomeomorph
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [Nonempty X] [T2Space Y] [PreconnectedSpace Y]
    {F : X → Y} (hF : IsLocalHomeomorph F) (hF_inj : Injective F) :
    Nonempty (X ≃ₜ Y) := by
  have hclosed : IsClosed (range F) :=
    (isCompact_range hF.continuous).isClosed
  have hsurj : Surjective F :=
    GlobalCoveringSkeleton.IsLocalHomeomorph.surjective_of_isClosed_range
      hF hclosed
  exact ⟨hF.toHomeomorphOfBijective ⟨hF_inj, hsurj⟩⟩

/--
The injective developing-map criterion discharges unit-curvature sphere
recognition without any additional global topology of the target sphere.
-/
theorem unitConstantCurvatureSphereRecognition3_of_injectiveLocalDevelopment
    (hdev : UnitCurvatureInjectiveLocalDevelopment3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  letI : PreconnectedSpace RoundSphere3 :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere
        (E := EuclideanSpace ℝ (Fin 4)) (by
          rw [← Module.finrank_eq_rank']
          simp) (0 : EuclideanSpace ℝ (Fin 4)) 1)
  intro g hcurv
  rcases hdev g hcurv with ⟨F, hF, hF_inj⟩
  simpa [RoundSphere3] using
    homeomorph_of_compact_injective_isLocalHomeomorph hF hF_inj

/--
A compact local homeomorphism over a simply connected, locally path connected
target is already a homeomorphism.  This is the precise covering-space
globalization consumed by the unit-curvature endgame.
-/
theorem homeomorph_of_compact_isLocalHomeomorph_simplyConnected
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [ConnectedSpace X]
    [SimplyConnectedSpace Y] [LocPathConnectedSpace Y]
    {F : X → Y} (hF : IsLocalHomeomorph F) :
    Nonempty (X ≃ₜ Y) := by
  have hcover : IsCoveringMap F :=
    GlobalCoveringSkeleton.isCoveringMap_of_compact_isLocalHomeomorph hF
  exact ⟨GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected hcover⟩

/--
Once the standard round three-sphere simple-connectivity fact is available,
a total local developing map is enough to discharge the full unit-curvature
recognition interface.  No injectivity or surjectivity hypothesis remains.
-/
theorem unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment
    (hSphereSimplyConnected : SimplyConnectedSpace RoundSphere3)
    (hdev : UnitCurvatureGlobalLocalDevelopment3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  letI : SimplyConnectedSpace RoundSphere3 := hSphereSimplyConnected
  letI : LocPathConnectedSpace RoundSphere3 :=
    ChartedSpace.locPathConnectedSpace (ClosedSmoothModel 3) RoundSphere3
  intro g hcurv
  rcases hdev g hcurv with ⟨F, hF⟩
  simpa [RoundSphere3] using
    homeomorph_of_compact_isLocalHomeomorph_simplyConnected hF

/--
Direct Cartan-gluing consumer for the unit-curvature recognition interface.
After the standard simple-connectivity theorem for the literal round sphere,
coherent continuation of the existing Cartan germs is the only hypothesis.
-/
theorem unitConstantCurvatureSphereRecognition3_of_coherentCartanGerms
    (hSphereSimplyConnected : SimplyConnectedSpace RoundSphere3)
    (hCartan : UnitCurvatureCoherentCartanGerms3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment
    hSphereSimplyConnected
    (globalLocalDevelopment_of_coherentCartanGerms hCartan)

/--
Pairwise-compatible anchored Cartan germs discharge unit-curvature
recognition after the standard round-sphere simple-connectivity fact.  The
total developing map, its local-homeomorphism property, injectivity, and
surjectivity have all been removed from the hypotheses.
-/
theorem unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
    (hSphereSimplyConnected : SimplyConnectedSpace RoundSphere3)
    (hAtlas : UnitCurvatureCompatibleCartanAtlas3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  unitConstantCurvatureSphereRecognition3_of_coherentCartanGerms
    hSphereSimplyConnected
    (coherentCartanGerms_of_compatibleCartanAtlas hAtlas)

/--
Final statement-chain consumer with the unit-recognition interface eliminated.
The geometric input is now universally quantified coherent Cartan-germ
continuation; the only target-side topological input is the standard simple
connectivity of the literal round three-sphere.
-/
theorem poincareConjecture_of_hamiltonConvergence_of_coherentCartanGerms
    (hSphereSimplyConnected : SimplyConnectedSpace RoundSphere3)
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3 N)
    (hCartan :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitCurvatureCoherentCartanGerms3 (M := N)) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergence_of_unitRecognition
    hHamilton
    (fun N _ _ _ _ _ _ _ _ ↦
      unitConstantCurvatureSphereRecognition3_of_coherentCartanGerms
        hSphereSimplyConnected (hCartan N))

/--
Strongest Cartan-atlas statement-chain consumer: pairwise overlap agreement of
the existing anchored Cartan germs replaces the entire unit-recognition
interface in the final Poincare composition.
-/
theorem poincareConjecture_of_hamiltonConvergence_of_compatibleCartanAtlas
    (hSphereSimplyConnected : SimplyConnectedSpace RoundSphere3)
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3 N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergence_of_unitRecognition
    hHamilton
    (fun N _ _ _ _ _ _ _ _ ↦
      unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
        hSphereSimplyConnected (hAtlas N))

end UnitRecognitionNext
end Poincare
