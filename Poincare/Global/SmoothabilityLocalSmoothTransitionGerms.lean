import Poincare.Global.SmoothabilityFiniteLocalAffineTransitionModels
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local smooth transition germs and compact finite extraction

The local-affine boundary is stronger than smoothability: exact local affine
coordinate changes would produce an affine atlas.  For the Moise smoothing
step, the natural Euclidean contract instead asks for arbitrary smooth local
extensions of the corrected transition germs.

This file proves that all finite patch bookkeeping follows from that local
statement.  Compactness extracts a finite subcover on every nerve edge, and a
smooth partition of unity blends the local extensions while preserving their
common value on the corrected compact transition domain.  Thus the only
remaining geometric input is the simultaneous choice of vertex corrections
with locally smoothly extendable corrected transition germs.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityLocalSmoothTransitionGerms

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => 𝓘(ℝ, E₃)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ambientChartedSpace : ChartedSpace E₃ M]

open SmoothabilityFiniteTransitionSmoothingBoundary
open SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3
open SmoothabilityFiniteSmoothTransitionExtension
open SmoothabilityFiniteLocalAffineTransitionModels
open SmoothabilityFiniteLocalAffineTransitionModels.NerveTransitionPackage3

abbrev PrecompactAtlas3 :=
  SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3
    data

/-- A finite family of arbitrary smooth local extensions of corrected
transition data.  Unlike the affine model contract, this asks only for the
regularity actually used by the partition-of-unity argument. -/
structure FiniteLocalSmoothTransitionModels3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) where
  correction : data.Index → OpenPartialHomeomorph E₃ E₃
  correction_neighborhood : ∀ i,
    data.compactCoordinateImage i ⊆ (correction i).source
  patchCount : ↑nerve.orderedPairs → ℕ
  patchDomain : ∀ p, Fin (patchCount p) → Set E₃
  isOpen_patchDomain : ∀ p q, IsOpen (patchDomain p q)
  patchMap : ∀ p, Fin (patchCount p) → E₃ → E₃
  patchMap_contDiffOn : ∀ p q,
    ContDiffOn ℝ ∞ (patchMap p q) (patchDomain p q)
  correctedCompactDomain_subset_patchCover : ∀ p,
    correction p.1.1 '' nerve.transitionDomain p ⊆
      ⋃ q, patchDomain p q
  patchMap_agrees_on_correctedCompactDomain :
    ∀ (p : ↑nerve.orderedPairs) (q : Fin (patchCount p)) (v : E₃),
      v ∈ nerve.transitionDomain p →
      correction p.1.1 v ∈ patchDomain p q →
        patchMap p q (correction p.1.1 v) =
          correction p.1.2 (nerve.transitionMap p v)

/-- The pointwise, non-finitary local smoothing contract. -/
def CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data)
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃) : Prop :=
  ∀ (p : ↑nerve.orderedPairs) (v : E₃),
    v ∈ nerve.transitionDomain p →
      ∃ U : Set E₃,
        IsOpen U ∧
        correction p.1.1 v ∈ U ∧
        ∃ f : E₃ → E₃,
          ContDiffOn ℝ ∞ f U ∧
          ∀ w : E₃,
            w ∈ nerve.transitionDomain p →
            correction p.1.1 w ∈ U →
              f (correction p.1.1 w) =
                correction p.1.2 (nerve.transitionMap p w)

/-- Local affine germs are, in particular, locally smoothly extendable
germs. -/
theorem locallySmoothlyExtendable_of_locallyAffine
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    {correction : data.Index → OpenPartialHomeomorph E₃ E₃}
    (hlocal : CorrectedTransitionsLocallyAffineOnCompact3
      data nerve correction) :
    CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
      data nerve correction := by
  intro p v hv
  obtain ⟨U, hUopen, hvU, A, hA⟩ := hlocal p v hv
  exact ⟨U, hUopen, hvU, A, A.contDiff.contDiffOn, hA⟩

/-- Compactness extracts finite local smooth models from pointwise local
smooth extension germs. -/
theorem nonempty_finiteLocalSmoothTransitionModels3_of_localGerms
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (hlocal : CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
      data nerve correction) :
    Nonempty (FiniteLocalSmoothTransitionModels3 data nerve) := by
  classical
  have hlocal' : ∀ (p : ↑nerve.orderedPairs)
      (v : {v : E₃ // v ∈ nerve.transitionDomain p}),
      ∃ U : Set E₃,
        IsOpen U ∧
        correction p.1.1 v.1 ∈ U ∧
        ∃ f : E₃ → E₃,
          ContDiffOn ℝ ∞ f U ∧
          ∀ w : E₃,
            w ∈ nerve.transitionDomain p →
            correction p.1.1 w ∈ U →
              f (correction p.1.1 w) =
                correction p.1.2 (nerve.transitionMap p w) :=
    fun p v ↦ hlocal p v.1 v.2
  choose U hUopen hUcenter f hfSmooth hfAgree using hlocal'
  have hcompact (p : ↑nerve.orderedPairs) :
      IsCompact (correction p.1.1 '' nerve.transitionDomain p) := by
    apply (nerve.isCompact_transitionDomain p).image_of_continuousOn
    exact (correction p.1.1).continuousOn.mono
      (Subset.trans
        (SmoothabilityFiniteLocalAffineTransitionModels.NerveTransitionPackage3.transitionDomain_subset_left_compactCoordinateImage
          nerve p)
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
      f p ((anchors p).equivFin.symm q).1
    patchMap_contDiffOn := fun p q ↦
      hfSmooth p ((anchors p).equivFin.symm q).1
    correctedCompactDomain_subset_patchCover := ?_
    patchMap_agrees_on_correctedCompactDomain := ?_
  }⟩
  · intro p y hy
    obtain ⟨v, hv, hyv⟩ := Set.mem_iUnion₂.1 (hanchors p hy)
    let v' : ↑(anchors p) := ⟨v, hv⟩
    exact Set.mem_iUnion.2 ⟨(anchors p).equivFin v', by
      simpa [v'] using hyv⟩
  · intro p q v hv hvpatch
    exact hfAgree p ((anchors p).equivFin.symm q).1 v hv hvpatch

namespace FiniteLocalSmoothTransitionModels3

variable {data : PrecompactAtlas3 M}
variable {nerve : NerveTransitionPackage3 data}

def correctedCompactDomain
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) : Set E₃ :=
  models.correction p.1.1 '' nerve.transitionDomain p

theorem isCompact_correctedCompactDomain
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    IsCompact (models.correctedCompactDomain p) := by
  apply (nerve.isCompact_transitionDomain p).image_of_continuousOn
  exact (models.correction p.1.1).continuousOn.mono
    (Subset.trans
      (SmoothabilityFiniteLocalAffineTransitionModels.NerveTransitionPackage3.transitionDomain_subset_left_compactCoordinateImage
        nerve p)
      (models.correction_neighborhood p.1.1))

theorem isClosed_correctedCompactDomain
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    IsClosed (models.correctedCompactDomain p) :=
  (models.isCompact_correctedCompactDomain p).isClosed

def patchUnion
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) : Set E₃ :=
  ⋃ q, models.patchDomain p q

theorem isOpen_patchUnion
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    IsOpen (models.patchUnion p) :=
  isOpen_iUnion fun q ↦ models.isOpen_patchDomain p q

noncomputable def smoothPartition
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    SmoothPartitionOfUnity (Fin (models.patchCount p)) I₃ E₃
      (models.correctedCompactDomain p) :=
  Classical.choose
    (SmoothPartitionOfUnity.exists_isSubordinate I₃
      (models.isClosed_correctedCompactDomain p)
      (models.patchDomain p)
      (models.isOpen_patchDomain p)
      (models.correctedCompactDomain_subset_patchCover p))

theorem smoothPartition_isSubordinate
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    (models.smoothPartition p).IsSubordinate (models.patchDomain p) :=
  Classical.choose_spec
    (SmoothPartitionOfUnity.exists_isSubordinate I₃
      (models.isClosed_correctedCompactDomain p)
      (models.patchDomain p)
      (models.isOpen_patchDomain p)
      (models.correctedCompactDomain_subset_patchCover p))

noncomputable def blendedExtension
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) (y : E₃) : E₃ :=
  ∑ᶠ q, models.smoothPartition p q y • models.patchMap p q y

theorem blendedExtension_contDiff
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) :
    ContDiff ℝ ∞ (models.blendedExtension p) := by
  have hMDiff : ContMDiff I₃ I₃ ∞ (models.blendedExtension p) := by
    exact (models.smoothPartition_isSubordinate p).contMDiff_finsum_smul
      (models.isOpen_patchDomain p)
      (fun q ↦ (models.patchMap_contDiffOn p q).contMDiffOn)
  exact hMDiff.contDiff

theorem blendedExtension_eq_correctedTransition
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) (v : E₃)
    (hv : v ∈ nerve.transitionDomain p) :
    models.blendedExtension p (models.correction p.1.1 v) =
      models.correction p.1.2 (nerve.transitionMap p v) := by
  let y : E₃ := models.correction p.1.1 v
  let target : E₃ := models.correction p.1.2 (nerve.transitionMap p v)
  have hy : y ∈ models.correctedCompactDomain p := ⟨v, hv, rfl⟩
  have hterm : ∀ q : Fin (models.patchCount p),
      models.smoothPartition p q y • models.patchMap p q y =
        models.smoothPartition p q y • target := by
    intro q
    by_cases hq : models.smoothPartition p q y = 0
    · simp [hq]
    · have hySupport :
          y ∈ Function.support (models.smoothPartition p q) :=
        Function.mem_support.2 hq
      have hyPatch : y ∈ models.patchDomain p q :=
        models.smoothPartition_isSubordinate p q
          (subset_closure hySupport)
      have hmodel : models.patchMap p q y = target := by
        simpa [y, target] using
          models.patchMap_agrees_on_correctedCompactDomain p q v hv hyPatch
      rw [hmodel]
  calc
    models.blendedExtension p (models.correction p.1.1 v) =
        ∑ᶠ q, models.smoothPartition p q y • models.patchMap p q y := by
          rfl
    _ = ∑ᶠ q, models.smoothPartition p q y • target :=
      finsum_congr hterm
    _ = (∑ᶠ q, models.smoothPartition p q y) • target :=
      (finsum_smul (fun q ↦ models.smoothPartition p q y) target).symm
    _ = target := by rw [models.smoothPartition p |>.sum_eq_one hy]; simp
    _ = models.correction p.1.2 (nerve.transitionMap p v) := rfl

noncomputable def toFiniteCompatibleSmoothTransitionExtensions3
    (models : FiniteLocalSmoothTransitionModels3 data nerve) :
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

noncomputable def toCInfinityLocalTransitionAtlasData3
    (models : FiniteLocalSmoothTransitionModels3 data nerve) :
    CInfinityLocalTransitionAtlasData3 M :=
  models.toFiniteCompatibleSmoothTransitionExtensions3
    |>.toCInfinityLocalTransitionAtlasData3

end FiniteLocalSmoothTransitionModels3

/-- The local smooth germ contract directly constructs the selected smooth
atlas; both finite reductions are internal consequences of compactness. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_localSmoothGerms
    (reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M)
    (correction : reduction.atlas.Index →
      OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      reduction.atlas.compactCoordinateImage i ⊆
        (correction i).source)
    (hlocal : CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
      reduction.atlas reduction.transitions correction) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨models⟩ :=
    nonempty_finiteLocalSmoothTransitionModels3_of_localGerms
      correction correction_neighborhood hlocal
  exact ⟨models.toCInfinityLocalTransitionAtlasData3⟩

/-- Universal local smooth-germ data is a finite-bookkeeping-free Moise
provider for the selected atlas boundary. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_localSmoothGermProvider3
    (provider : ∀ reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M,
      ∃ correction : reduction.atlas.Index →
          OpenPartialHomeomorph E₃ E₃,
        (∀ i, reduction.atlas.compactCoordinateImage i ⊆
          (correction i).source) ∧
        CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
          reduction.atlas reduction.transitions correction) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨reduction⟩ :=
    SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3
      (M := M)
  obtain ⟨correction, hneighborhood, hlocal⟩ := provider reduction
  exact nonempty_cInfinityLocalTransitionAtlasData3_of_localSmoothGerms
    reduction correction hneighborhood hlocal

end SmoothabilityLocalSmoothTransitionGerms
end Poincare
