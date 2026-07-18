import Poincare.Global.RoundSphereSimpleConnected

/-!
# Cartan gluing on restricted anchor domains

The full compatible-Cartan-atlas interface asks two anchored Cartan germs to
agree on the whole intersection of their maximal packaged sources.  For local
development this is stronger than necessary.  It is enough to choose, at each
anchor, an open neighborhood contained in that source and prove pairwise
agreement only on intersections of the chosen neighborhoods.

This restricted interface is designed for quantitative domain shrinking: the
chosen neighborhood may additionally lie in a metric ball on which terminal
normal coordinates are uniformly small.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace UnitRecognitionNext

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- One anchored Cartan family together with smaller open domains on which
pairwise compatibility is known. -/
structure RestrictedCompatibleCartanAtlasData3
    (g : ClosedSmoothRiemannianMetric 3 M) where
  target : M → RoundSphere3
  alignment : ∀ x : M, CartanMap.TangentAlignment g x (target x)
  domain : M → Set M
  isOpen_domain : ∀ x : M, IsOpen (domain x)
  anchor_mem_domain : ∀ x : M, x ∈ domain x
  domain_subset_source : ∀ x : M,
    domain x ⊆
      (CartanMap.openPartialHomeomorph
        g x (target x) (alignment x)).source
  compatible : ∀ x y : M,
    EqOn
      (CartanMap.openPartialHomeomorph
        g x (target x) (alignment x))
      (CartanMap.openPartialHomeomorph
        g y (target y) (alignment y))
      (domain x ∩ domain y)

namespace RestrictedCompatibleCartanAtlasData3

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- The full packaged Cartan germ underneath one restricted atlas member. -/
def germ (data : RestrictedCompatibleCartanAtlasData3 g) (x : M) :
    OpenPartialHomeomorph M RoundSphere3 :=
  CartanMap.openPartialHomeomorph
    g x (data.target x) (data.alignment x)

/-- The diagonal gluing: evaluate at `z` the selected germ anchored at `z`. -/
def diagonalDevelopment
    (data : RestrictedCompatibleCartanAtlasData3 g) : M → RoundSphere3 :=
  fun z ↦ data.germ z z

/-- Restricted pairwise compatibility identifies the diagonal development
with each anchored germ throughout that member's chosen domain. -/
theorem diagonalDevelopment_eqOn_domain
    (data : RestrictedCompatibleCartanAtlasData3 g) (x : M) :
    EqOn data.diagonalDevelopment (data.germ x) (data.domain x) := by
  intro z hz
  exact data.compatible z x ⟨data.anchor_mem_domain z, hz⟩

/-- The diagonal development is locally a restriction of the full Cartan
partial homeomorphism at every anchor. -/
theorem isLocalHomeomorph_diagonalDevelopment
    (data : RestrictedCompatibleCartanAtlasData3 g) :
    IsLocalHomeomorph data.diagonalDevelopment := by
  apply IsLocalHomeomorph.mk
  intro x
  let e : OpenPartialHomeomorph M RoundSphere3 :=
    (data.germ x).restrOpen (data.domain x) (data.isOpen_domain x)
  refine ⟨e, ?_, ?_⟩
  · change x ∈ (data.germ x).source ∩ data.domain x
    exact
      ⟨data.domain_subset_source x (data.anchor_mem_domain x),
        data.anchor_mem_domain x⟩
  · intro z hz
    change data.diagonalDevelopment z = data.germ x z
    apply data.diagonalDevelopment_eqOn_domain x
    change z ∈ (data.germ x).source ∩ data.domain x at hz
    exact hz.2

end RestrictedCompatibleCartanAtlasData3

/-- Unit-curvature recognition data with compatibility required only on a
chosen open neighborhood of every anchor. -/
def UnitCurvatureRestrictedCompatibleCartanAtlas3 : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      Nonempty (RestrictedCompatibleCartanAtlasData3 g)

/-- Restricted compatible Cartan domains glue to the same total local
development consumed by the covering-space endgame. -/
theorem globalLocalDevelopment_of_restrictedCompatibleCartanAtlas
    (hAtlas : UnitCurvatureRestrictedCompatibleCartanAtlas3 (M := M)) :
    UnitCurvatureGlobalLocalDevelopment3 (M := M) := by
  intro g hcurv
  rcases hAtlas g hcurv with ⟨data⟩
  exact
    ⟨data.diagonalDevelopment,
      data.isLocalHomeomorph_diagonalDevelopment⟩

/-- Restricted compatible Cartan domains suffice for unit-curvature sphere
recognition once the target sphere's simple connectivity is supplied. -/
theorem unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
    (hSphereSimplyConnected : SimplyConnectedSpace RoundSphere3)
    (hAtlas : UnitCurvatureRestrictedCompatibleCartanAtlas3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment
    hSphereSimplyConnected
    (globalLocalDevelopment_of_restrictedCompatibleCartanAtlas hAtlas)

end UnitRecognitionNext

namespace RoundSphereSimpleConnected

/-- Restricted compatible Cartan domains discharge unit-curvature recognition
with the round-sphere topology supplied internally. -/
theorem unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
    {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (hAtlas :
      UnitRecognitionNext.UnitCurvatureRestrictedCompatibleCartanAtlas3
        (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  UnitRecognitionNext.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
    roundSphere3_simplyConnectedSpace hAtlas

end RoundSphereSimpleConnected
end Poincare
