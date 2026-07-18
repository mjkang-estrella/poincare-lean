import Poincare.Global.SmoothabilityFiniteSmoothTransitionExtension
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite local-affine transition models

The compact transition-extension boundary is reduced here to finite local
Euclidean data.  After choosing one topological coordinate correction at each
vertex, cover every corrected compact transition domain by finitely many open
sets.  On each member of the cover, supply a continuous affine map which
agrees with the corrected topological transition wherever the compact domain
meets that member.

A smooth partition of unity subordinate to the finite open cover blends the
affine maps into a single globally smooth Euclidean map.  Since every
nonzero partition coefficient at a point of the compact domain is subordinate
to a patch on which its affine model has the prescribed value, the blend
agrees *exactly* with the corrected transition there.  Thus the local-affine
data constructs `FiniteCompatibleSmoothTransitionExtensions3`.

The contract below stores no smoothness assertion, no pairwise compatibility
between affine models, no charted-space instance, and no manifold-recognition
conclusion.  Compatibility on the compact transition set is sufficient:
convex blending removes the need to glue the affine maps literally on their
open overlaps.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityFiniteLocalAffineTransitionModels

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ambientChartedSpace : ChartedSpace E₃ M]

open SmoothabilityFiniteTransitionSmoothingBoundary
open SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3
open SmoothabilityFiniteSmoothTransitionExtension

abbrev PrecompactAtlas3 :=
  SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3
    data

namespace NerveTransitionPackage3

variable {data : PrecompactAtlas3 M}

/-- A compact transition domain is contained in the compact coordinate image
of its left-hand chart vertex. -/
theorem transitionDomain_subset_left_compactCoordinateImage
    (nerve : NerveTransitionPackage3 data)
    (p : ↑nerve.orderedPairs) :
    nerve.transitionDomain p ⊆ data.compactCoordinateImage p.1.1 := by
  rw [nerve.transitionDomain_eq p]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, closure_mono inter_subset_left hx, rfl⟩

end NerveTransitionPackage3

/-- Finite local-affine data for all corrected transition domains.

For an ordered nerve edge `p`, `patchCount p` gives a genuinely finite family
of open Euclidean patches.  Their union covers the corrected compact
transition domain.  The affine model on a patch is required to have the
correct value only at points of that compact domain which lie in the patch.
No agreement between two affine models away from the compact domain is
required. -/
structure FiniteLocalAffineTransitionModels3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) where
  correction : data.Index → OpenPartialHomeomorph E₃ E₃
  correction_neighborhood : ∀ i,
    data.compactCoordinateImage i ⊆ (correction i).source
  patchCount : ↑nerve.orderedPairs → ℕ
  patchDomain : ∀ p, Fin (patchCount p) → Set E₃
  isOpen_patchDomain : ∀ p q, IsOpen (patchDomain p q)
  patchMap : ∀ p, Fin (patchCount p) → E₃ →ᴬ[ℝ] E₃
  correctedCompactDomain_subset_patchCover : ∀ p,
    correction p.1.1 '' nerve.transitionDomain p ⊆
      ⋃ q, patchDomain p q
  patchMap_agrees_on_correctedCompactDomain :
    ∀ (p : ↑nerve.orderedPairs) (q : Fin (patchCount p)) (v : E₃),
      v ∈ nerve.transitionDomain p →
      correction p.1.1 v ∈ patchDomain p q →
        patchMap p q (correction p.1.1 v) =
          correction p.1.2 (nerve.transitionMap p v)

/-- Pointwise local-affine regularity of the corrected compact transitions.

This is the non-finitary local statement hidden inside
`FiniteLocalAffineTransitionModels3`: at every point of every compact nerve
transition domain, one affine map represents the corrected transition on the
part of that compact domain lying in some open neighborhood of the corrected
point.  There is no chosen family of neighborhoods, no patch index, and no
finite-cover field.

The condition is deliberately relative to the compact transition domain.  It
does not claim that a merely piecewise-affine map is locally affine across a
simplex face.  A PL smoothing theorem must construct vertex corrections for
which this stronger local statement holds. -/
def CorrectedTransitionsLocallyAffineOnCompact3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data)
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃) : Prop :=
  ∀ (p : ↑nerve.orderedPairs) (v : E₃),
    v ∈ nerve.transitionDomain p →
      ∃ U : Set E₃,
        IsOpen U ∧
        correction p.1.1 v ∈ U ∧
        ∃ A : E₃ →ᴬ[ℝ] E₃,
          ∀ w : E₃,
            w ∈ nerve.transitionDomain p →
            correction p.1.1 w ∈ U →
              A (correction p.1.1 w) =
                correction p.1.2 (nerve.transitionMap p w)

/-- Compactness turns pointwise local-affine germs into the finite patch
family required by `FiniteLocalAffineTransitionModels3`.

In particular, finiteness of the affine family is not part of the geometric
smoothing problem: it follows formally from compactness of each nerve
transition domain. -/
theorem nonempty_finiteLocalAffineTransitionModels3_of_locallyAffineOnCompact
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (hlocal : CorrectedTransitionsLocallyAffineOnCompact3
      data nerve correction) :
    Nonempty (FiniteLocalAffineTransitionModels3 data nerve) := by
  classical
  have hlocal' : ∀ (p : ↑nerve.orderedPairs)
      (v : {v : E₃ // v ∈ nerve.transitionDomain p}),
      ∃ U : Set E₃,
        IsOpen U ∧
        correction p.1.1 v.1 ∈ U ∧
        ∃ A : E₃ →ᴬ[ℝ] E₃,
          ∀ w : E₃,
            w ∈ nerve.transitionDomain p →
            correction p.1.1 w ∈ U →
              A (correction p.1.1 w) =
                correction p.1.2 (nerve.transitionMap p w) :=
    fun p v ↦ hlocal p v.1 v.2
  choose U hUopen hUcenter A hA using hlocal'
  have hcompact (p : ↑nerve.orderedPairs) :
      IsCompact (correction p.1.1 '' nerve.transitionDomain p) := by
    apply (nerve.isCompact_transitionDomain p).image_of_continuousOn
    exact (correction p.1.1).continuousOn.mono
      (Subset.trans
        (nerve.transitionDomain_subset_left_compactCoordinateImage p)
        (correction_neighborhood p.1.1))
  have hfinite : ∀ p : ↑nerve.orderedPairs,
      ∃ anchors : Finset {v : E₃ // v ∈ nerve.transitionDomain p},
        correction p.1.1 '' nerve.transitionDomain p ⊆
          ⋃ v ∈ anchors, U p v := by
    intro p
    apply (hcompact p).elim_finite_subcover (U p) (hUopen p)
    rintro _ ⟨v, hv, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨v, hv⟩, hUcenter p ⟨v, hv⟩⟩
  choose anchors hanchors using hfinite
  refine ⟨{
    correction := correction
    correction_neighborhood := correction_neighborhood
    patchCount := fun p ↦ (anchors p).card
    patchDomain := fun p q ↦
      U p ((anchors p).equivFin.symm q).1
    isOpen_patchDomain := fun p q ↦
      hUopen p ((anchors p).equivFin.symm q).1
    patchMap := fun p q ↦
      A p ((anchors p).equivFin.symm q).1
    correctedCompactDomain_subset_patchCover := ?_
    patchMap_agrees_on_correctedCompactDomain := ?_
  }⟩
  · intro p y hy
    obtain ⟨v, hv, hyv⟩ := Set.mem_iUnion₂.1 (hanchors p hy)
    let v' : ↑(anchors p) := ⟨v, hv⟩
    exact Set.mem_iUnion.2 ⟨(anchors p).equivFin v', by
      simpa [v'] using hyv⟩
  · intro p q v hv hvpatch
    exact hA p ((anchors p).equivFin.symm q).1 v hv hvpatch

/-- Conversely, a finite local-affine model has the pointwise local affine
germs from which compactness extracted it. -/
theorem correctedTransitionsLocallyAffineOnCompact3_of_finiteModels
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (models : FiniteLocalAffineTransitionModels3 data nerve) :
    CorrectedTransitionsLocallyAffineOnCompact3
      data nerve models.correction := by
  intro p v hv
  have hvImage : models.correction p.1.1 v ∈
      models.correction p.1.1 '' nerve.transitionDomain p :=
    ⟨v, hv, rfl⟩
  obtain ⟨q, hvq⟩ := Set.mem_iUnion.1
    (models.correctedCompactDomain_subset_patchCover p hvImage)
  exact ⟨models.patchDomain p q, models.isOpen_patchDomain p q, hvq,
    models.patchMap p q, fun w hw hwq ↦
      models.patchMap_agrees_on_correctedCompactDomain p q w hw hwq⟩

/-- Exact contract equivalence: finite patch administration contributes no
geometric content beyond pointwise local-affine corrected transition germs.
Compactness supplies the finite family in the reverse direction. -/
theorem nonempty_finiteLocalAffineTransitionModels3_iff_exists_localGerms
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data} :
    Nonempty (FiniteLocalAffineTransitionModels3 data nerve) ↔
      ∃ correction : data.Index → OpenPartialHomeomorph E₃ E₃,
        (∀ i, data.compactCoordinateImage i ⊆ (correction i).source) ∧
        CorrectedTransitionsLocallyAffineOnCompact3
          data nerve correction := by
  constructor
  · rintro ⟨models⟩
    exact ⟨models.correction, models.correction_neighborhood,
      correctedTransitionsLocallyAffineOnCompact3_of_finiteModels models⟩
  · rintro ⟨correction, hneighborhood, hlocal⟩
    exact
      nonempty_finiteLocalAffineTransitionModels3_of_locallyAffineOnCompact
        correction hneighborhood hlocal

namespace FiniteLocalAffineTransitionModels3

variable {data : PrecompactAtlas3 M}
variable {nerve : NerveTransitionPackage3 data}

/-- The compact set on which the local affine models prescribe a corrected
transition. -/
def correctedCompactDomain
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) : Set E₃ :=
  models.correction p.1.1 '' nerve.transitionDomain p

/-- The corrected transition domain is compact. -/
theorem isCompact_correctedCompactDomain
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    IsCompact (models.correctedCompactDomain p) := by
  apply (nerve.isCompact_transitionDomain p).image_of_continuousOn
  exact (models.correction p.1.1).continuousOn.mono
    (Subset.trans
      (nerve.transitionDomain_subset_left_compactCoordinateImage p)
      (models.correction_neighborhood p.1.1))

/-- The corrected transition domain is closed in Euclidean space. -/
theorem isClosed_correctedCompactDomain
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    IsClosed (models.correctedCompactDomain p) :=
  (models.isCompact_correctedCompactDomain p).isClosed

/-- The open neighborhood obtained by taking the union of the finitely many
local affine patches. -/
def patchUnion
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) : Set E₃ :=
  ⋃ q, models.patchDomain p q

/-- The finite patch union is open. -/
theorem isOpen_patchUnion
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    IsOpen (models.patchUnion p) :=
  isOpen_iUnion fun q ↦ models.isOpen_patchDomain p q

/-- Choose a smooth partition of unity on the corrected compact domain,
subordinate to the supplied finite affine patch cover. -/
noncomputable def affinePartition
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    SmoothPartitionOfUnity (Fin (models.patchCount p)) I₃ E₃
      (models.correctedCompactDomain p) :=
  Classical.choose
    (SmoothPartitionOfUnity.exists_isSubordinate I₃
      (models.isClosed_correctedCompactDomain p)
      (models.patchDomain p)
      (models.isOpen_patchDomain p)
      (models.correctedCompactDomain_subset_patchCover p))

/-- The chosen partition is subordinate to the local affine patches. -/
theorem affinePartition_isSubordinate
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    (models.affinePartition p).IsSubordinate (models.patchDomain p) :=
  Classical.choose_spec
    (SmoothPartitionOfUnity.exists_isSubordinate I₃
      (models.isClosed_correctedCompactDomain p)
      (models.patchDomain p)
      (models.isOpen_patchDomain p)
      (models.correctedCompactDomain_subset_patchCover p))

/-- Blend the local affine transition models with the subordinate smooth
partition.  The result is defined on all of Euclidean space. -/
noncomputable def blendedExtension
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) (y : E₃) : E₃ :=
  ∑ᶠ q, models.affinePartition p q y • models.patchMap p q y

/-- The blended extension is globally `C∞`. -/
theorem blendedExtension_contDiff
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    ContDiff ℝ ∞ (models.blendedExtension p) := by
  have hMDiff : ContMDiff I₃ I₃ ∞ (models.blendedExtension p) := by
    exact (models.affinePartition_isSubordinate p).contMDiff_finsum_smul
      (models.isOpen_patchDomain p)
      (fun q ↦ (models.patchMap p q).contDiff.contMDiff.contMDiffOn)
  exact hMDiff.contDiff

/-- At a point of the corrected compact domain, every partition coefficient
which is nonzero selects a patch whose affine map has the prescribed
corrected-transition value. -/
theorem blendedExtension_eq_correctedTransition
    (models : FiniteLocalAffineTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) (v : E₃)
    (hv : v ∈ nerve.transitionDomain p) :
    models.blendedExtension p (models.correction p.1.1 v) =
      models.correction p.1.2 (nerve.transitionMap p v) := by
  let y : E₃ := models.correction p.1.1 v
  let target : E₃ := models.correction p.1.2 (nerve.transitionMap p v)
  have hy : y ∈ models.correctedCompactDomain p := ⟨v, hv, rfl⟩
  have hterm : ∀ q : Fin (models.patchCount p),
      models.affinePartition p q y • models.patchMap p q y =
        models.affinePartition p q y • target := by
    intro q
    by_cases hq : models.affinePartition p q y = 0
    · simp [hq]
    · have hySupport :
          y ∈ Function.support (models.affinePartition p q) :=
        Function.mem_support.2 hq
      have hyPatch : y ∈ models.patchDomain p q :=
        models.affinePartition_isSubordinate p q
          (subset_closure hySupport)
      have hmodel : models.patchMap p q y = target := by
        simpa [y, target] using
          models.patchMap_agrees_on_correctedCompactDomain p q v hv hyPatch
      rw [hmodel]
  calc
    models.blendedExtension p (models.correction p.1.1 v) =
        ∑ᶠ q, models.affinePartition p q y • models.patchMap p q y := by
          rfl
    _ = ∑ᶠ q, models.affinePartition p q y • target :=
      finsum_congr hterm
    _ = (∑ᶠ q, models.affinePartition p q y) • target :=
      (finsum_smul (fun q ↦ models.affinePartition p q y) target).symm
    _ = target := by rw [models.affinePartition p |>.sum_eq_one hy]; simp
    _ = models.correction p.1.2 (nerve.transitionMap p v) := rfl

/-- Finite local affine models construct the preceding compact-domain smooth
extension contract.  The extension neighborhood and the smooth extension are
both derived, not stored. -/
noncomputable def toFiniteCompatibleSmoothTransitionExtensions3
    (models : FiniteLocalAffineTransitionModels3 data nerve) :
    FiniteCompatibleSmoothTransitionExtensions3 data nerve where
  correction := models.correction
  correction_neighborhood := models.correction_neighborhood
  extensionNeighborhood := models.patchUnion
  isOpen_extensionNeighborhood := models.isOpen_patchUnion
  correctedCompactDomain_subset_extensionNeighborhood :=
    models.correctedCompactDomain_subset_patchCover
  smoothExtension := models.blendedExtension
  smoothExtension_contDiffOn := fun p ↦
    (models.blendedExtension_contDiff p).contDiffOn
  smoothExtension_agrees_on_compactDomain := fun p v hv ↦
    models.blendedExtension_eq_correctedTransition p v hv

/-- Consequently, finite local affine models construct the actual finite
simultaneous transition-smoothing witness. -/
noncomputable def toFiniteSimultaneousTransitionSmoothingExtension3
    (models : FiniteLocalAffineTransitionModels3 data nerve) :
    FiniteSimultaneousTransitionSmoothingExtension3 data nerve :=
  models.toFiniteCompatibleSmoothTransitionExtensions3
    |>.toFiniteSimultaneousTransitionSmoothingExtension3

/-- Consequently, finite local affine models construct the proof-bearing
local `C∞` transition atlas. -/
noncomputable def toCInfinityLocalTransitionAtlasData3
    (models : FiniteLocalAffineTransitionModels3 data nerve) :
    CInfinityLocalTransitionAtlasData3 M :=
  models.toFiniteCompatibleSmoothTransitionExtensions3
    |>.toCInfinityLocalTransitionAtlasData3

end FiniteLocalAffineTransitionModels3

/-- A finite nerve reduction together with local affine transition models is
enough for the selected proof-bearing smooth-transition atlas. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_finiteLocalAffineTransitionModels3
    (reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M)
    (models : FiniteLocalAffineTransitionModels3
      reduction.atlas reduction.transitions) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) :=
  ⟨models.toCInfinityLocalTransitionAtlasData3⟩

/-- Pointwise local-affine corrected transition germs already construct the
proof-bearing smooth-transition atlas.  The intermediate finite patch family
is extracted by compactness. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_locallyAffineOnCompact
    (reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M)
    (correction : reduction.atlas.Index →
      OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      reduction.atlas.compactCoordinateImage i ⊆
        (correction i).source)
    (hlocal : CorrectedTransitionsLocallyAffineOnCompact3
      reduction.atlas reduction.transitions correction) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨models⟩ :=
    nonempty_finiteLocalAffineTransitionModels3_of_locallyAffineOnCompact
      correction correction_neighborhood hlocal
  exact
    nonempty_cInfinityLocalTransitionAtlasData3_of_finiteLocalAffineTransitionModels3
      reduction models

/-- A universal solver for the finite local-affine transition problem closes
the selected smooth-transition-atlas boundary.  Compactness supplies the
finite nerve reduction before the provider is invoked. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_finiteLocalAffineTransitionModelsProvider3
    (provider : ∀ reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M,
      Nonempty (FiniteLocalAffineTransitionModels3
        reduction.atlas reduction.transitions)) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨reduction⟩ :=
    SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3
      (M := M)
  exact
    nonempty_cInfinityLocalTransitionAtlasData3_of_finiteLocalAffineTransitionModels3
      reduction (provider reduction).some

/-- A universal local-germ solver is the exact remaining Moise-style input
needed by this route.  Compactness supplies both the finite atlas nerve and
the finite affine subcovers; neither finiteness assertion remains in the
provider. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_localAffineGermProvider3
    (provider : ∀ reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M,
      ∃ correction : reduction.atlas.Index →
          OpenPartialHomeomorph E₃ E₃,
        (∀ i, reduction.atlas.compactCoordinateImage i ⊆
          (correction i).source) ∧
        CorrectedTransitionsLocallyAffineOnCompact3
          reduction.atlas reduction.transitions correction) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨reduction⟩ :=
    SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3
      (M := M)
  obtain ⟨correction, hneighborhood, hlocal⟩ := provider reduction
  exact
    nonempty_cInfinityLocalTransitionAtlasData3_of_locallyAffineOnCompact
      reduction correction hneighborhood hlocal

end SmoothabilityFiniteLocalAffineTransitionModels
end Poincare
