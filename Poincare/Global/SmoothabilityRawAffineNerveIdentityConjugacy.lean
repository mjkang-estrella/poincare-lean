import Poincare.Global.SmoothabilityPLCompatibleAffineConjugacy

/-!
# Identity conjugacy for an already locally affine finite atlas nerve

This file isolates a sufficient special case of the PL-compatible affine
conjugacy boundary.  Suppose every raw transition of one finite precompact
atlas nerve is, relative to its compact transition domain, locally equal to a
continuous affine equivalence.  Then no coordinate modification is needed:
the genuine identity open partial homeomorphism at every atlas vertex is a
valid simultaneous correction.

The identity corrections are defined on all of Euclidean space, so their
neighborhood fields are automatic.  Their applications simplify to the
identity on both sides of every corrected transition equation, reducing the
existing corrected affine-conjugacy predicate exactly to the raw condition.
The finite-subcover and smooth-local-diffeomorphism construction from
`SmoothabilityPLCompatibleAffineConjugacy` then supplies simultaneous
smoothing and proof-bearing `C∞` atlas data.

This is deliberately an *already locally affine atlas* criterion.  It does
not prove that an arbitrary PL atlas admits such local affine models at
simplex faces, and it is not a general PL-smoothing or Moise theorem.  No
one-point compactification or sphere-recognition statement is used.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityRawAffineNerveIdentityConjugacy

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

open SmoothabilityFinitePrecompactTopologicalAtlasReduction
open SmoothabilityFiniteAtlasNerveReduction
open SmoothabilityPLCompatibleAffineConjugacy
open SmoothabilitySimultaneousLocalConjugacy

abbrev PrecompactAtlas3 :=
  FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  FiniteAtlasNerveTransitionPackage3 data

abbrev NerveReduction3 := FiniteAtlasNerveReduction3

/-- Every raw nerve transition is locally represented by a continuous affine
equivalence on its compact transition domain.

Agreement is required only for points `w` which lie both in the compact
transition domain and in the selected open patch.  In particular, no claim is
made about the junk extension of `nerve.transitionMap p` away from its honest
compact domain. -/
def RawTransitionsLocallyAffineEquivOnCompact3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) : Prop :=
  ∀ (p : ↑nerve.orderedPairs) (v : E₃),
    v ∈ nerve.transitionDomain p →
      ∃ U : Set E₃,
        IsOpen U ∧
        v ∈ U ∧
        ∃ A : E₃ ≃ᴬ[ℝ] E₃,
          ∀ w : E₃,
            w ∈ nerve.transitionDomain p →
            w ∈ U →
              A w = nerve.transitionMap p w

/-- The simultaneous vertex correction used for an already locally affine
nerve: the identity open partial homeomorphism on all of Euclidean space. -/
def identityVertexCorrection (data : PrecompactAtlas3 M) :
    data.Index → OpenPartialHomeomorph E₃ E₃ :=
  fun _ ↦ OpenPartialHomeomorph.refl E₃

@[simp]
theorem identityVertexCorrection_source
    (data : PrecompactAtlas3 M) (i : data.Index) :
    (identityVertexCorrection data i).source = Set.univ := by
  simp [identityVertexCorrection]

@[simp]
theorem identityVertexCorrection_apply
    (data : PrecompactAtlas3 M) (i : data.Index) (v : E₃) :
    identityVertexCorrection data i v = v := by
  simp [identityVertexCorrection]

/-- Identity corrections are defined on a neighborhood of every compact
coordinate image because their source is the whole model space. -/
theorem compactCoordinateImage_subset_identityVertexCorrection_source
    (data : PrecompactAtlas3 M) (i : data.Index) :
    data.compactCoordinateImage i ⊆
      (identityVertexCorrection data i).source := by
  simp

/-- With identity corrections, the corrected affine-equivalence condition is
exactly the raw transition condition above. -/
theorem correctedTransitionsLocallyAffineEquivOnCompact3_identity_iff
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) :
    CorrectedTransitionsLocallyAffineEquivOnCompact3
        data nerve (identityVertexCorrection data) ↔
      RawTransitionsLocallyAffineEquivOnCompact3 data nerve := by
  constructor
  · intro hcorrected p v hv
    obtain ⟨U, hUopen, hvU, A, hA⟩ := hcorrected p v hv
    refine ⟨U, hUopen, ?_, A, ?_⟩
    · simpa using hvU
    · intro w hw hwU
      simpa using hA w hw (by simpa using hwU)
  · intro hraw p v hv
    obtain ⟨U, hUopen, hvU, A, hA⟩ := hraw p v hv
    refine ⟨U, hUopen, ?_, A, ?_⟩
    · simpa using hvU
    · intro w hw hwU
      simpa using hA w hw (by simpa using hwU)

/-- An already locally affine finite nerve constructs the PL-compatible
affine-conjugacy package with genuine identity vertex corrections. -/
def finiteNervePLCompatibleAffineConjugacy3_of_rawTransitionsLocallyAffineEquiv
    (reduction : NerveReduction3 M)
    (hraw : RawTransitionsLocallyAffineEquivOnCompact3
      reduction.atlas reduction.transitions) :
    FiniteNervePLCompatibleAffineConjugacy3 reduction where
  correction := identityVertexCorrection reduction.atlas
  correction_neighborhood :=
    compactCoordinateImage_subset_identityVertexCorrection_source
      reduction.atlas
  local_affine_equiv :=
    (correctedTransitionsLocallyAffineEquivOnCompact3_identity_iff
      reduction.atlas reduction.transitions).2 hraw

/-- The existing compact finite-subcover construction turns the identity
affine-conjugacy package into simultaneous smooth local conjugacies. -/
noncomputable def
    finiteNerveSimultaneousLocalConjugacySmoothing3_of_rawTransitionsLocallyAffineEquiv
    (reduction : NerveReduction3 M)
    (hraw : RawTransitionsLocallyAffineEquivOnCompact3
      reduction.atlas reduction.transitions) :
    FiniteNerveSimultaneousLocalConjugacySmoothing3 reduction :=
  (finiteNervePLCompatibleAffineConjugacy3_of_rawTransitionsLocallyAffineEquiv
    reduction hraw).toFiniteNerveSimultaneousLocalConjugacySmoothing3

/-- Consequently, an already locally affine finite nerve supplies the
proof-bearing `C∞` transition atlas selected by the smoothability reduction. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_rawTransitionsLocallyAffineEquiv
    (reduction : NerveReduction3 M)
    (hraw : RawTransitionsLocallyAffineEquivOnCompact3
      reduction.atlas reduction.transitions) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) :=
  (finiteNerveSimultaneousLocalConjugacySmoothing3_of_rawTransitionsLocallyAffineEquiv
    reduction hraw).nonempty_cInfinityLocalTransitionAtlasData3

end SmoothabilityRawAffineNerveIdentityConjugacy
end Poincare
