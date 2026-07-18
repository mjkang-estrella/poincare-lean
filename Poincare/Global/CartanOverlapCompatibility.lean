import Poincare.Global.UnitRecognitionNext
import Poincare.Global.ExpNaturality

/-!
# Cartan overlap compatibility from re-centered exponential naturality

This module sharpens the remaining Cartan globalization boundary in two ways.

First, a family of anchored Cartan germs is pairwise compatible exactly when
it can be compared with one coherent total reference map.  Thus the compatible
atlas and coherent-germ interfaces in `UnitRecognitionNext` are equivalent;
pairwise compatibility is not an additional geometric burden.

Second, the one-step and all-anchor overlap conclusions are derived directly
from the charted re-centered exponential identity.  This is the identity
naturally produced before applying target-chart inverses, so no auxiliary
membership hypothesis for the *old* Cartan value in the new target chart is
needed.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanOverlapCompatibility

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Agreement of every member of a family with one reference map on its own domain
implies pairwise agreement on all domain intersections.
-/
theorem pairwise_eqOn_of_eqOn_reference
    {J X Y : Type*} {G : J → X → Y} {U : J → Set X} {F : X → Y}
    (hF : ∀ j : J, EqOn F (G j) (U j)) (i j : J) :
    EqOn (G i) (G j) (U i ∩ U j) := by
  intro x hx
  exact (hF i hx.1).symm.trans (hF j hx.2)

/--
A coherent total Cartan map canonically supplies a pairwise-compatible Cartan
atlas.  The anchors and tangent alignments are chosen from the coherent germ
at each point; pairwise agreement is then transitivity through the total map.
-/
theorem compatibleCartanAtlas_of_coherentCartanGerms
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hCartan : UnitRecognitionNext.UnitCurvatureCoherentCartanGerms3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) := by
  intro g hcurv
  rcases hCartan g hcurv with ⟨F, hF⟩
  choose p L hFL using hF
  refine ⟨p, L, ?_⟩
  intro x y
  exact pairwise_eqOn_of_eqOn_reference hFL x y

/--
The coherent-germ and pairwise-compatible-atlas globalization payloads are
equivalent.  The forward implication is the reference-map argument above; the
reverse implication is the canonical diagonal gluing construction.
-/
theorem compatibleCartanAtlas_iff_coherentCartanGerms
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) ↔
      UnitRecognitionNext.UnitCurvatureCoherentCartanGerms3 (M := M) := by
  constructor
  · exact UnitRecognitionNext.coherentCartanGerms_of_compatibleCartanAtlas
  · exact compatibleCartanAtlas_of_coherentCartanGerms

/--
The charted target-ray identity is already exactly the explicitly re-anchored
Cartan map.  Consequently it proves a rigid compatible step without any
separate target-chart source hypothesis for the old carried value.
-/
theorem rigidStepCompatibleWith_of_charted_target_ray
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁))
    (htarget :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        s.map x =
          (chartAt E (s.map x₁)).symm
            (GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (s.map x₁)
              (L₁
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) x₁).symm ((chartAt E x₁) x))))) :
    InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x₁ L₁ := by
  intro x hx
  change s.map x = CartanMap.cartanMap g x₁ (s.map x₁) L₁ x
  exact htarget x hx

/--
All-anchor charted re-centering payload.  It is the pairwise version of
`rigidStepCompatibleWith_of_charted_target_ray`: the germ anchored at `x`,
when written in the normal coordinates anchored at `y`, has the canonical
Cartan exponential formula determined by `L y`.
-/
def UnitCurvatureChartedRecenterNaturality3
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ (p : M → RoundSphere3)
        (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
          ∀ x y z : M,
            z ∈ (CartanMap.openPartialHomeomorph g x (p x) (L x)).source ∩
              (CartanMap.openPartialHomeomorph g y (p y) (L y)).source →
              CartanMap.cartanMap g x (p x) (L x) z =
                (chartAt E (p y)).symm
                  (GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := roundSphereMetric3) (p y)
                    (L y
                      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                        (g := g) y).symm ((chartAt E y) z))))

/--
All-anchor charted re-centered exponential naturality closes the precise
pairwise `EqOn` overlap requested by the compatible Cartan atlas interface.
-/
theorem compatibleCartanAtlas_of_chartedRecenterNaturality
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hNaturality : UnitCurvatureChartedRecenterNaturality3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) := by
  intro g hcurv
  rcases hNaturality g hcurv with ⟨p, L, hnatural⟩
  refine ⟨p, L, ?_⟩
  intro x y z hz
  change CartanMap.cartanMap g x (p x) (L x) z =
    CartanMap.cartanMap g y (p y) (L y) z
  exact hnatural x y z hz

/--
The charted re-centering identity therefore discharges the geometric Cartan
globalization input of unit-curvature sphere recognition.  Only the independent
topological fact that the literal round-sphere model is simply connected
remains as a target-side argument.
-/
theorem unitConstantCurvatureSphereRecognition3_of_chartedRecenterNaturality
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hSphereSimplyConnected : SimplyConnectedSpace RoundSphere3)
    (hNaturality : UnitCurvatureChartedRecenterNaturality3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  UnitRecognitionNext.unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
    hSphereSimplyConnected
    (compatibleCartanAtlas_of_chartedRecenterNaturality hNaturality)

end CartanOverlapCompatibility
end Poincare
