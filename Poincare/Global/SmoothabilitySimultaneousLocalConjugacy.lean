import Poincare.Global.SmoothabilityLocalSmoothTransitionGerms

/-!
# Simultaneous local-conjugacy boundary for three-dimensional smoothing

The legacy Moise/PL records in `Poincare.Smoothability` are not usable as an
independent smoothing input: their first field is already a homeomorphism with
the one-point compactification of `R^3`.  This file instead states the local
output that a noncircular PL-smoothing theorem must provide.

For the finite precompact atlas supplied by compactness, choose one topological
coordinate correction at every vertex.  On every compact nerve transition and
at every one of its points, the corrected transition must agree locally with a
genuine smooth local diffeomorphism.  The choices of vertex corrections are
simultaneous across all edges; no smooth atlas, manifold structure, or sphere
recognition is stored in the contract.

The main theorem below converts this local-conjugacy output to the already
verified local smooth-germ provider.  All subsequent finite-cover,
partition-of-unity, and charted-space assembly steps are therefore formal
consequences.  The remaining topological theorem is exactly the universal
existence of `FiniteNerveSimultaneousLocalConjugacySmoothing3`.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilitySimultaneousLocalConjugacy

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

open SmoothabilityFinitePrecompactTopologicalAtlasReduction
open SmoothabilityFiniteAtlasNerveReduction
open SmoothabilityLocalSmoothTransitionGerms

abbrev PrecompactAtlas3 :=
  FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  FiniteAtlasNerveTransitionPackage3 data

abbrev NerveReduction3 := FiniteAtlasNerveReduction3

/-- A smooth local diffeomorphism between open subsets of Euclidean
three-space.  Both directions are recorded because this is the natural local
output of smoothing a PL coordinate change, even though only forward
smoothness is needed by the atlas-construction reduction. -/
structure SmoothLocalDiffeomorphism3 where
  toOpenPartialHomeomorph : OpenPartialHomeomorph E₃ E₃
  forward_contDiffOn :
    ContDiffOn ℝ ∞ toOpenPartialHomeomorph
      toOpenPartialHomeomorph.source
  inverse_contDiffOn :
    ContDiffOn ℝ ∞ toOpenPartialHomeomorph.symm
      toOpenPartialHomeomorph.target

namespace SmoothLocalDiffeomorphism3

instance : CoeFun SmoothLocalDiffeomorphism3 (fun _ ↦ E₃ → E₃) :=
  ⟨fun e ↦ e.toOpenPartialHomeomorph⟩

@[simp]
theorem source_symm (e : SmoothLocalDiffeomorphism3) :
    e.toOpenPartialHomeomorph.symm.source =
      e.toOpenPartialHomeomorph.target :=
  rfl

end SmoothLocalDiffeomorphism3

/-- The corrected transition has a smooth local-diffeomorphism conjugacy germ
at every point of every compact nerve transition.

The agreement is deliberately relative to the compact transition domain.
This includes boundary points of the overlap closure and is exactly strong
enough for the finite smooth-extension construction. -/
def CorrectedTransitionsLocallySmoothlyConjugateOnCompact3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data)
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃) : Prop :=
  ∀ (p : ↑nerve.orderedPairs) (v : E₃),
    v ∈ nerve.transitionDomain p →
      ∃ e : SmoothLocalDiffeomorphism3,
        correction p.1.1 v ∈ e.toOpenPartialHomeomorph.source ∧
        ∀ w : E₃,
          w ∈ nerve.transitionDomain p →
          correction p.1.1 w ∈ e.toOpenPartialHomeomorph.source →
            e (correction p.1.1 w) =
              correction p.1.2 (nerve.transitionMap p w)

/-- A smooth local-conjugacy germ is, after forgetting invertibility of its
local model, a locally smoothly extendable corrected transition germ. -/
theorem locallySmoothlyExtendable_of_locallySmoothlyConjugate
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    {correction : data.Index → OpenPartialHomeomorph E₃ E₃}
    (hlocal : CorrectedTransitionsLocallySmoothlyConjugateOnCompact3
      data nerve correction) :
    CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
      data nerve correction := by
  intro p v hv
  obtain ⟨e, hvSource, hAgree⟩ := hlocal p v hv
  exact ⟨e.toOpenPartialHomeomorph.source,
    e.toOpenPartialHomeomorph.open_source, hvSource,
    e.toOpenPartialHomeomorph, e.forward_contDiffOn,
    fun w hw hwSource ↦ hAgree w hw hwSource⟩

/-- The narrow simultaneous output expected from a three-dimensional
PL-smoothing/local-conjugacy theorem for one finite atlas nerve.

There is one correction per atlas vertex, shared by every incident edge.  The
record contains neither a smooth atlas nor any topological recognition of the
underlying manifold. -/
structure FiniteNerveSimultaneousLocalConjugacySmoothing3
    (reduction : NerveReduction3 M) where
  correction : reduction.atlas.Index → OpenPartialHomeomorph E₃ E₃
  correction_neighborhood : ∀ i,
    reduction.atlas.compactCoordinateImage i ⊆ (correction i).source
  local_conjugacy :
    CorrectedTransitionsLocallySmoothlyConjugateOnCompact3
      reduction.atlas reduction.transitions correction

namespace FiniteNerveSimultaneousLocalConjugacySmoothing3

/-- Forgetting the local inverse-smoothness data gives the exact local-germ
triple consumed by the existing finite smoothability reduction. -/
theorem toLocalSmoothGerms
    {reduction : NerveReduction3 M}
    (smoothing :
      FiniteNerveSimultaneousLocalConjugacySmoothing3 reduction) :
    ∃ correction : reduction.atlas.Index →
        OpenPartialHomeomorph E₃ E₃,
      (∀ i, reduction.atlas.compactCoordinateImage i ⊆
        (correction i).source) ∧
      CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
        reduction.atlas reduction.transitions correction :=
  ⟨smoothing.correction, smoothing.correction_neighborhood,
    locallySmoothlyExtendable_of_locallySmoothlyConjugate
      smoothing.local_conjugacy⟩

/-- One simultaneous local-conjugacy smoothing package constructs the selected
proof-bearing smooth-transition atlas. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3
    {reduction : NerveReduction3 M}
    (smoothing :
      FiniteNerveSimultaneousLocalConjugacySmoothing3 reduction) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨correction, hneighborhood, hlocal⟩ := smoothing.toLocalSmoothGerms
  exact nonempty_cInfinityLocalTransitionAtlasData3_of_localSmoothGerms
    reduction correction hneighborhood hlocal

end FiniteNerveSimultaneousLocalConjugacySmoothing3

/-- Universal finite-nerve local conjugacy is the standalone, noncircular
Moise/PL smoothing statement left by the reduction in this repository. -/
def UniversalFiniteNerveLocalConjugacySmoothing3 : Prop :=
  ∀ reduction : NerveReduction3 M,
    Nonempty (FiniteNerveSimultaneousLocalConjugacySmoothing3 reduction)

/-- A universal simultaneous local-conjugacy solver supplies the exact local
smooth-germ provider, with all finite topology already discharged. -/
theorem localSmoothGermProvider3_of_universalFiniteNerveLocalConjugacySmoothing3
    (h : UniversalFiniteNerveLocalConjugacySmoothing3 (M := M)) :
    ∀ reduction : NerveReduction3 M,
      ∃ correction : reduction.atlas.Index →
          OpenPartialHomeomorph E₃ E₃,
        (∀ i, reduction.atlas.compactCoordinateImage i ⊆
          (correction i).source) ∧
        CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
          reduction.atlas reduction.transitions correction := by
  intro reduction
  exact (h reduction).some.toLocalSmoothGerms

/-- The universal noncircular local-conjugacy theorem closes the selected
smooth-atlas existence boundary. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_universalFiniteNerveLocalConjugacySmoothing3
    (h : UniversalFiniteNerveLocalConjugacySmoothing3 (M := M)) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) :=
  nonempty_cInfinityLocalTransitionAtlasData3_of_localSmoothGermProvider3
    (localSmoothGermProvider3_of_universalFiniteNerveLocalConjugacySmoothing3 h)

end SmoothabilitySimultaneousLocalConjugacy
end Poincare
