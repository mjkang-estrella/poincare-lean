import Poincare.Global.SmoothabilityFiniteLocalAffineTransitionModels
import Poincare.Global.SmoothabilitySimultaneousLocalConjugacy
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# PL-compatible affine conjugacy implies finite-nerve smoothing

The simultaneous local-conjugacy boundary asks for genuine smooth local
diffeomorphisms, while the preceding affine reduction only constructs smooth
maps: a general affine map need not be locally invertible.  This file isolates
the extra, noncircular datum needed to bridge that gap.

For every compact nerve transition, require pointwise agreement on an open
neighborhood with a *continuous affine equivalence*.  Compactness extracts a
finite family of such neighborhoods.  Restricting each global affine
equivalence to its open patch gives a smooth local diffeomorphism; both its
forward map and inverse are smooth because both are continuous affine maps.
Selecting a covering patch at each compact-domain point then proves the exact
local-conjugacy predicate used by
`FiniteNerveSimultaneousLocalConjugacySmoothing3`.

The input below stores no smoothness assertion, smooth atlas, manifold
structure, one-point compactification, or sphere-recognition statement.  It is
the finite-atlas bookkeeping output that a noncircular PL-compatible
coordinate theorem can supply.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityPLCompatibleAffineConjugacy

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

open SmoothabilityFinitePrecompactTopologicalAtlasReduction
open SmoothabilityFiniteAtlasNerveReduction
open SmoothabilitySimultaneousLocalConjugacy

abbrev PrecompactAtlas3 :=
  FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  FiniteAtlasNerveTransitionPackage3 data

abbrev NerveReduction3 := FiniteAtlasNerveReduction3

/-! ## Pointwise and finite locally invertible affine data -/

/-- Pointwise locally invertible affine regularity of corrected compact
transitions.

The agreement is relative to the compact transition domain, including its
boundary.  The affine equivalence is global, but it need only agree with the
corrected transition on the supplied open patch. -/
def CorrectedTransitionsLocallyAffineEquivOnCompact3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data)
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃) : Prop :=
  ∀ (p : ↑nerve.orderedPairs) (v : E₃),
    v ∈ nerve.transitionDomain p →
      ∃ U : Set E₃,
        IsOpen U ∧
        correction p.1.1 v ∈ U ∧
        ∃ A : E₃ ≃ᴬ[ℝ] E₃,
          ∀ w : E₃,
            w ∈ nerve.transitionDomain p →
            correction p.1.1 w ∈ U →
              A (correction p.1.1 w) =
                correction p.1.2 (nerve.transitionMap p w)

/-- A finite open-patch presentation of locally invertible affine corrected
transitions.  Unlike `FiniteLocalAffineTransitionModels3`, every patch map is
an affine equivalence, so its restriction is a local diffeomorphism. -/
structure FiniteLocalAffineEquivConjugacyModels3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) where
  correction : data.Index → OpenPartialHomeomorph E₃ E₃
  correction_neighborhood : ∀ i,
    data.compactCoordinateImage i ⊆ (correction i).source
  patchCount : ↑nerve.orderedPairs → ℕ
  patchDomain : ∀ p, Fin (patchCount p) → Set E₃
  isOpen_patchDomain : ∀ p q, IsOpen (patchDomain p q)
  patchEquiv : ∀ p, Fin (patchCount p) → E₃ ≃ᴬ[ℝ] E₃
  correctedCompactDomain_subset_patchCover : ∀ p,
    correction p.1.1 '' nerve.transitionDomain p ⊆
      ⋃ q, patchDomain p q
  patchEquiv_agrees_on_correctedCompactDomain :
    ∀ (p : ↑nerve.orderedPairs) (q : Fin (patchCount p)) (v : E₃),
      v ∈ nerve.transitionDomain p →
      correction p.1.1 v ∈ patchDomain p q →
        patchEquiv p q (correction p.1.1 v) =
          correction p.1.2 (nerve.transitionMap p v)

/-- Compactness extracts a finite affine-equivalence patch family from the
pointwise local condition.  Thus finiteness is bookkeeping, not an additional
geometric hypothesis. -/
theorem nonempty_finiteLocalAffineEquivConjugacyModels3_of_local
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (hlocal : CorrectedTransitionsLocallyAffineEquivOnCompact3
      data nerve correction) :
    Nonempty (FiniteLocalAffineEquivConjugacyModels3 data nerve) := by
  classical
  have hlocal' : ∀ (p : ↑nerve.orderedPairs)
      (v : {v : E₃ // v ∈ nerve.transitionDomain p}),
      ∃ U : Set E₃,
        IsOpen U ∧
        correction p.1.1 v.1 ∈ U ∧
        ∃ A : E₃ ≃ᴬ[ℝ] E₃,
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
    patchEquiv := fun p q ↦
      A p ((anchors p).equivFin.symm q).1
    correctedCompactDomain_subset_patchCover := ?_
    patchEquiv_agrees_on_correctedCompactDomain := ?_
  }⟩
  · intro p y hy
    obtain ⟨v, hv, hyv⟩ := Set.mem_iUnion₂.1 (hanchors p hy)
    let v' : ↑(anchors p) := ⟨v, hv⟩
    exact Set.mem_iUnion.2 ⟨(anchors p).equivFin v', by
      simpa [v'] using hyv⟩
  · intro p q v hv hvpatch
    exact hA p ((anchors p).equivFin.symm q).1 v hv hvpatch

/-- A finite affine-equivalence model recovers the pointwise local condition
from which compactness extracted it. -/
theorem correctedTransitionsLocallyAffineEquivOnCompact3_of_finiteModels
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (models : FiniteLocalAffineEquivConjugacyModels3 data nerve) :
    CorrectedTransitionsLocallyAffineEquivOnCompact3
      data nerve models.correction := by
  intro p v hv
  have hvImage : models.correction p.1.1 v ∈
      models.correction p.1.1 '' nerve.transitionDomain p :=
    ⟨v, hv, rfl⟩
  obtain ⟨q, hvq⟩ := Set.mem_iUnion.1
    (models.correctedCompactDomain_subset_patchCover p hvImage)
  exact ⟨models.patchDomain p q, models.isOpen_patchDomain p q, hvq,
    models.patchEquiv p q, fun w hw hwq ↦
      models.patchEquiv_agrees_on_correctedCompactDomain p q w hw hwq⟩

/-- Exact equivalence between the pointwise geometric condition and its finite
patch administration. -/
theorem nonempty_finiteLocalAffineEquivConjugacyModels3_iff_exists_local
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data} :
    Nonempty (FiniteLocalAffineEquivConjugacyModels3 data nerve) ↔
      ∃ correction : data.Index → OpenPartialHomeomorph E₃ E₃,
        (∀ i, data.compactCoordinateImage i ⊆ (correction i).source) ∧
        CorrectedTransitionsLocallyAffineEquivOnCompact3
          data nerve correction := by
  constructor
  · rintro ⟨models⟩
    exact ⟨models.correction, models.correction_neighborhood,
      correctedTransitionsLocallyAffineEquivOnCompact3_of_finiteModels models⟩
  · rintro ⟨correction, hneighborhood, hlocal⟩
    exact nonempty_finiteLocalAffineEquivConjugacyModels3_of_local
      correction hneighborhood hlocal

namespace FiniteLocalAffineEquivConjugacyModels3

variable {data : PrecompactAtlas3 M}
variable {nerve : NerveTransitionPackage3 data}

/-- Forget invertibility and recover the pre-existing finite local-affine
transition-model contract. -/
def toFiniteLocalAffineTransitionModels3
    (models : FiniteLocalAffineEquivConjugacyModels3 data nerve) :
    SmoothabilityFiniteLocalAffineTransitionModels.FiniteLocalAffineTransitionModels3
      data nerve where
  correction := models.correction
  correction_neighborhood := models.correction_neighborhood
  patchCount := models.patchCount
  patchDomain := models.patchDomain
  isOpen_patchDomain := models.isOpen_patchDomain
  patchMap := fun p q ↦ (models.patchEquiv p q).toContinuousAffineMap
  correctedCompactDomain_subset_patchCover :=
    models.correctedCompactDomain_subset_patchCover
  patchMap_agrees_on_correctedCompactDomain := fun p q v hv hvq ↦ by
    exact models.patchEquiv_agrees_on_correctedCompactDomain p q v hv hvq

/-- Restrict one global affine equivalence to its selected open patch.  This
is a smooth local diffeomorphism, with inverse smoothness derived from the
inverse continuous affine equivalence. -/
def affinePatchLocalDiffeomorphism
    (models : FiniteLocalAffineEquivConjugacyModels3 data nerve)
    (p : ↑nerve.orderedPairs) (q : Fin (models.patchCount p)) :
    SmoothLocalDiffeomorphism3 where
  toOpenPartialHomeomorph :=
    (models.patchEquiv p q).toHomeomorph.toOpenPartialHomeomorph.restrOpen
      (models.patchDomain p q) (models.isOpen_patchDomain p q)
  forward_contDiffOn := by
    simpa using
      (models.patchEquiv p q).toContinuousAffineMap.contDiff.contDiffOn
  inverse_contDiffOn := by
    simpa using
      (models.patchEquiv p q).symm.toContinuousAffineMap.contDiff.contDiffOn

@[simp]
theorem affinePatchLocalDiffeomorphism_source
    (models : FiniteLocalAffineEquivConjugacyModels3 data nerve)
    (p : ↑nerve.orderedPairs) (q : Fin (models.patchCount p)) :
    (models.affinePatchLocalDiffeomorphism p q).toOpenPartialHomeomorph.source =
      models.patchDomain p q := by
  simp [affinePatchLocalDiffeomorphism]

@[simp]
theorem affinePatchLocalDiffeomorphism_apply
    (models : FiniteLocalAffineEquivConjugacyModels3 data nerve)
    (p : ↑nerve.orderedPairs) (q : Fin (models.patchCount p)) (x : E₃) :
    models.affinePatchLocalDiffeomorphism p q x = models.patchEquiv p q x :=
  rfl

/-- Finite affine-equivalence patches give the exact pointwise smooth local
conjugacies required by the simultaneous finite-nerve boundary. -/
theorem correctedTransitionsLocallySmoothlyConjugateOnCompact3
    (models : FiniteLocalAffineEquivConjugacyModels3 data nerve) :
    CorrectedTransitionsLocallySmoothlyConjugateOnCompact3
      data nerve models.correction := by
  intro p v hv
  have hvImage : models.correction p.1.1 v ∈
      models.correction p.1.1 '' nerve.transitionDomain p :=
    ⟨v, hv, rfl⟩
  obtain ⟨q, hvq⟩ := Set.mem_iUnion.1
    (models.correctedCompactDomain_subset_patchCover p hvImage)
  refine ⟨models.affinePatchLocalDiffeomorphism p q, ?_, ?_⟩
  · simpa only [affinePatchLocalDiffeomorphism_source] using hvq
  · intro w hw hwSource
    rw [affinePatchLocalDiffeomorphism_apply]
    exact models.patchEquiv_agrees_on_correctedCompactDomain p q w hw
      (by
        simpa only [affinePatchLocalDiffeomorphism_source] using hwSource)

/-- The finite affine-equivalence model constructs the target simultaneous
local-conjugacy smoothing record. -/
def toFiniteNerveSimultaneousLocalConjugacySmoothing3
    {reduction : NerveReduction3 M}
    (models : FiniteLocalAffineEquivConjugacyModels3
      reduction.atlas reduction.transitions) :
    FiniteNerveSimultaneousLocalConjugacySmoothing3 reduction where
  correction := models.correction
  correction_neighborhood := models.correction_neighborhood
  local_conjugacy :=
    models.correctedTransitionsLocallySmoothlyConjugateOnCompact3

end FiniteLocalAffineEquivConjugacyModels3

/-! ## A narrow PL-compatible input for one finite nerve -/

/-- The affine-conjugacy package expected from a noncircular PL-compatible
coordinate theorem for one finite atlas nerve.

There is one correction per vertex, shared across all incident nerve edges.
Only pointwise locally invertible affine agreement is assumed; compactness and
all finite patch choices are derived below. -/
structure FiniteNervePLCompatibleAffineConjugacy3
    (reduction : NerveReduction3 M) where
  correction : reduction.atlas.Index → OpenPartialHomeomorph E₃ E₃
  correction_neighborhood : ∀ i,
    reduction.atlas.compactCoordinateImage i ⊆ (correction i).source
  local_affine_equiv :
    CorrectedTransitionsLocallyAffineEquivOnCompact3
      reduction.atlas reduction.transitions correction

namespace FiniteNervePLCompatibleAffineConjugacy3

/-- Compactness converts the pointwise PL-compatible affine input into its
finite patch presentation. -/
theorem finiteModels
    {reduction : NerveReduction3 M}
    (input : FiniteNervePLCompatibleAffineConjugacy3 reduction) :
    Nonempty (FiniteLocalAffineEquivConjugacyModels3
      reduction.atlas reduction.transitions) :=
  nonempty_finiteLocalAffineEquivConjugacyModels3_of_local
    input.correction input.correction_neighborhood input.local_affine_equiv

/-- The PL-compatible affine input yields the exact simultaneous
local-conjugacy smoothing record, with the finite subcover and smooth inverse
bookkeeping discharged internally. -/
noncomputable def toFiniteNerveSimultaneousLocalConjugacySmoothing3
    {reduction : NerveReduction3 M}
    (input : FiniteNervePLCompatibleAffineConjugacy3 reduction) :
    FiniteNerveSimultaneousLocalConjugacySmoothing3 reduction :=
  input.finiteModels.some.toFiniteNerveSimultaneousLocalConjugacySmoothing3

end FiniteNervePLCompatibleAffineConjugacy3

/-- A direct pointwise locally invertible affine hypothesis produces a
finite-nerve simultaneous smoothing witness. -/
theorem nonempty_finiteNerveSimultaneousLocalConjugacySmoothing3_of_localAffineEquiv
    (reduction : NerveReduction3 M)
    (correction : reduction.atlas.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      reduction.atlas.compactCoordinateImage i ⊆ (correction i).source)
    (hlocal : CorrectedTransitionsLocallyAffineEquivOnCompact3
      reduction.atlas reduction.transitions correction) :
    Nonempty (FiniteNerveSimultaneousLocalConjugacySmoothing3 reduction) := by
  obtain ⟨models⟩ :=
    nonempty_finiteLocalAffineEquivConjugacyModels3_of_local
      correction correction_neighborhood hlocal
  exact ⟨models.toFiniteNerveSimultaneousLocalConjugacySmoothing3⟩

/-- Universal existence of the explicit PL-compatible affine input implies
the remaining universal simultaneous local-conjugacy boundary. -/
theorem universalFiniteNerveLocalConjugacySmoothing3_of_plCompatibleAffineConjugacy
    (provider : ∀ reduction : NerveReduction3 M,
      Nonempty (FiniteNervePLCompatibleAffineConjugacy3 reduction)) :
    UniversalFiniteNerveLocalConjugacySmoothing3 (M := M) := by
  intro reduction
  exact (provider reduction).map
    FiniteNervePLCompatibleAffineConjugacy3.toFiniteNerveSimultaneousLocalConjugacySmoothing3

/-- Consequently, a universal PL-compatible affine-conjugacy provider closes
the already verified proof-bearing smooth-atlas boundary. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_plCompatibleAffineConjugacyProvider
    (provider : ∀ reduction : NerveReduction3 M,
      Nonempty (FiniteNervePLCompatibleAffineConjugacy3 reduction)) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) :=
  nonempty_cInfinityLocalTransitionAtlasData3_of_universalFiniteNerveLocalConjugacySmoothing3
    (universalFiniteNerveLocalConjugacySmoothing3_of_plCompatibleAffineConjugacy
      provider)

end SmoothabilityPLCompatibleAffineConjugacy
end Poincare
