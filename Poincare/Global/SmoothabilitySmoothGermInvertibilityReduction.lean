import Poincare.Global.SmoothabilityAffineGermInvertibilityReduction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Smooth corrected transition germs have smooth local inverses

The compact transition domains are closures of actual open overlaps. Smooth
extensions for both ordered directions therefore have inverse derivatives,
including at boundary points, by continuity from that open overlap. The
inverse function theorem upgrades these extensions to local diffeomorphisms.
The vertex corrections and their local smooth extensions remain inputs.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilitySmoothGermInvertibilityReduction

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

open SmoothabilityFinitePrecompactTopologicalAtlasReduction
open SmoothabilityFiniteAtlasNerveReduction
open SmoothabilityFiniteLocalAffineTransitionModels
open SmoothabilityLocalSmoothTransitionGerms
open SmoothabilitySimultaneousLocalConjugacy
open SmoothabilityAffineGermInvertibilityReduction

section EuclideanCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inverse identity on an open set forces inverse derivatives even at
its boundary, when both maps are globally smooth. -/
theorem smooth_inverse_derivative_at_closure_global
    {f g : E → E} {O : Set E} {x : E}
    (hO : IsOpen O) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hx : x ∈ closure O) (hinv : EqOn (g ∘ f) id O) :
    (fderiv ℝ g (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E := by
  have heq : EqOn (fderiv ℝ (g ∘ f)) (fun _ ↦ ContinuousLinearMap.id ℝ E) O := by
    intro y hy
    have hlocal : (g ∘ f) =ᶠ[𝓝 y] id := by
      filter_upwards [hO.mem_nhds hy] with z hz
      exact hinv hz
    simpa using hlocal.fderiv_eq (𝕜 := ℝ)
  have hlim := heq.closure ((hg.comp hf).continuous_fderiv (by simp)) continuous_const hx
  rw [fderiv_comp x (hg.differentiable (by simp) (f x)) (hf.differentiable (by simp) x)] at hlim
  exact hlim

/-- A left-inverse derivative is bijective for a finite-dimensional
endomorphism. -/
theorem smooth_derivative_bijective_at_closure_global
    [FiniteDimensional ℝ E]
    {f g : E → E} {O : Set E} {x : E}
    (hO : IsOpen O) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hx : x ∈ closure O) (hinv : EqOn (g ∘ f) id O) :
    Function.Bijective (fderiv ℝ f x) := by
  have hcomp := smooth_inverse_derivative_at_closure_global hO hf hg hx hinv
  have hleft : Function.LeftInverse (fderiv ℝ g (f x)) (fderiv ℝ f x) := by
    intro a
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun A : E →L[ℝ] E ↦ A a) hcomp
  exact ⟨hleft.injective, LinearMap.surjective_of_injective hleft.injective⟩

end EuclideanCalculus

section EuclideanLocalInverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth map with invertible derivative is a smooth local
diffeomorphism on one fixed neighborhood within its given smooth domain. -/
theorem localDiffeoOfSmoothOn {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (e : E ≃L[ℝ] F) (he : (e : E →L[ℝ] F) = fderiv ℝ f x) :
    ∃ q : OpenPartialHomeomorph E F, x ∈ q.source ∧
      q.source ⊆ U ∧ (q : E → F) = f ∧
      ContDiffOn ℝ ∞ q q.source ∧ ContDiffOn ℝ ∞ q.symm q.target := by
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hfx' : HasFDerivAt f (e : E →L[ℝ] F) x := by
    rw [he]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  have hDf : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hx)
  have hInv : (fderiv ℝ f) ⁻¹' range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) ∈ 𝓝 x := by
    apply hDf.preimage_mem_nhds
    rw [← he]
    exact e.nhds
  obtain ⟨V, hV, hVopen, hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hInv)
  let q₀ := hfx.toOpenPartialHomeomorph f hfx' (by simp)
  let q := q₀.restrOpen V hVopen
  have hqf : (q : E → F) = f := rfl
  have hSource : q.source ⊆ U := fun _ hy ↦ (hV hy.2).1
  refine ⟨q, ⟨hfx.mem_toOpenPartialHomeomorph_source hfx' (by simp), hxV⟩,
    hSource, hqf, ?_, ?_⟩
  · rw [hqf]
    exact hf.mono hSource
  · apply q.open_target.contDiffOn_iff.mpr
    intro y hy
    have hqy : q.symm y ∈ q.source := q.map_target hy
    obtain ⟨ey, hey⟩ := (hV hqy.2).2
    have hfy : ContDiffAt ℝ ∞ f (q.symm y) :=
      hf.contDiffAt (hU.mem_nhds (hSource hqy))
    apply q.contDiffAt_symm hy (f₀' := ey)
    · rw [hqf, hey]
      exact (hfy.differentiableAt (by simp)).hasFDerivAt
    · rw [hqf]
      exact hfy

section FiniteDimensional
variable [FiniteDimensional ℝ E]

/-- Global smoothness and one bijective derivative produce a smooth local
inverse, with the forward map preserved literally. -/
theorem localDiffeoOfSmooth {f : E → F} {x : E}
    (hf : ContDiff ℝ ∞ f) (hbij : Function.Bijective (fderiv ℝ f x)) :
    ∃ q : OpenPartialHomeomorph E F, x ∈ q.source ∧
      (q : E → F) = f ∧ ContDiffOn ℝ ∞ q q.source ∧
      ContDiffOn ℝ ∞ q.symm q.target := by
  let e : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] F) = fderiv ℝ f x := by
    ext z
    rfl
  obtain ⟨q, hxq, _, hqf, hq, hqinv⟩ :=
    localDiffeoOfSmoothOn isOpen_univ (mem_univ x) hf.contDiffOn e he
  exact ⟨q, hxq, hqf, hq, hqinv⟩
end FiniteDimensional

end EuclideanLocalInverse

/-- Reverse an actual ordered overlap edge, using symmetry of the nerve. -/
def reversePair
    {data : FinitePrecompactTopologicalChartAtAtlas3 M}
    (nerve : FiniteAtlasNerveTransitionPackage3 data)
    (p : ↑nerve.orderedPairs) : ↑nerve.orderedPairs :=
  ⟨(p.1.2, p.1.1), (nerve.pair_mem_iff _).2
    (data.nerveRel_symm ((nerve.pair_mem_iff _).1 p.2))⟩

/-- The actual reverse transition carries the compact forward image back
to its initial coordinate. -/
theorem reverse_transition_on_compactDomain
    {data : FinitePrecompactTopologicalChartAtAtlas3 M}
    (nerve : FiniteAtlasNerveTransitionPackage3 data)
    (p : ↑nerve.orderedPairs) {v : E₃}
    (hv : v ∈ nerve.transitionDomain p) :
    nerve.transitionMap p v ∈ nerve.transitionDomain (reversePair nerve p) ∧
      nerve.transitionMap (reversePair nerve p) (nerve.transitionMap p v) = v := by
  rw [nerve.transitionDomain_eq p] at hv
  rcases hv with ⟨x, hx, rfl⟩
  have hxrev : x ∈ closure (data.overlap p.1.2 p.1.1) := by
    simpa [FinitePrecompactTopologicalChartAtAtlas3.overlap, inter_comm] using hx
  rw [nerve.transition_agrees_on_overlapClosure p x hx]
  constructor
  · rw [nerve.transitionDomain_eq]
    exact ⟨x, hxrev, rfl⟩
  · exact nerve.transition_agrees_on_overlapClosure (reversePair nerve p) x hxrev

/-- Compact extraction can retain the supplied vertex corrections literally.
This extra equality permits use of the global smooth blended extensions
without changing the corrections in the local-conjugacy conclusion. -/
theorem exists_finiteLocalSmoothModels_with_correction
    {data : FinitePrecompactTopologicalChartAtAtlas3 M}
    {nerve : FiniteAtlasNerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (hlocal : CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
      data nerve correction) :
    ∃ models : FiniteLocalSmoothTransitionModels3 data nerve,
      models.correction = correction := by
  classical
  have hlocal' : ∀ (p : ↑nerve.orderedPairs)
      (v : {v : E₃ // v ∈ nerve.transitionDomain p}),
      ∃ U : Set E₃,
        IsOpen U ∧ correction p.1.1 v.1 ∈ U ∧
        ∃ f : E₃ → E₃,
          ContDiffOn ℝ ∞ f U ∧
          ∀ w : E₃, w ∈ nerve.transitionDomain p →
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
        (NerveTransitionPackage3.transitionDomain_subset_left_compactCoordinateImage
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
    patchDomain := fun p q ↦ U p ((anchors p).equivFin.symm q).1
    isOpen_patchDomain := fun p q ↦ hUopen p ((anchors p).equivFin.symm q).1
    patchMap := fun p q ↦ f p ((anchors p).equivFin.symm q).1
    patchMap_contDiffOn := fun p q ↦ hfSmooth p ((anchors p).equivFin.symm q).1
    correctedCompactDomain_subset_patchCover := ?_
    patchMap_agrees_on_correctedCompactDomain := ?_
  }, rfl⟩
  · intro p y hy
    obtain ⟨v, hv, hyv⟩ := Set.mem_iUnion₂.1 (hanchors p hy)
    let v' : ↑(anchors p) := ⟨v, hv⟩
    exact Set.mem_iUnion.2 ⟨(anchors p).equivFin v', by
      simpa [v'] using hyv⟩
  · intro p q v hv hvpatch
    exact hfAgree p ((anchors p).equivFin.symm q).1 v hv hvpatch

/-- The globally smooth models for reverse edges compose to the identity on
the corrected compact transition, and hence on its genuine open part. -/
theorem blended_reverse_comp_on_compactDomain
    {data : FinitePrecompactTopologicalChartAtAtlas3 M}
    {nerve : FiniteAtlasNerveTransitionPackage3 data}
    (models : FiniteLocalSmoothTransitionModels3 data nerve)
    (p : ↑nerve.orderedPairs) {v : E₃}
    (hv : v ∈ nerve.transitionDomain p) :
    models.blendedExtension (reversePair nerve p)
        (models.blendedExtension p (models.correction p.1.1 v)) =
      models.correction p.1.1 v := by
  obtain ⟨hvrev, hrev⟩ := reverse_transition_on_compactDomain nerve p hv
  rw [models.blendedExtension_eq_correctedTransition p v hv]
  calc
    models.blendedExtension (reversePair nerve p)
        (models.correction p.1.2 (nerve.transitionMap p v)) =
        models.correction p.1.1
          (nerve.transitionMap (reversePair nerve p) (nerve.transitionMap p v)) := by
      simpa only [reversePair] using
        models.blendedExtension_eq_correctedTransition
          (reversePair nerve p) (nerve.transitionMap p v) hvrev
    _ = models.correction p.1.1 v := congrArg (models.correction p.1.1) hrev

/-- Smooth local extensions in both ordered directions automatically give
smooth local diffeomorphism germs. The supplied corrections are preserved.

The derivative identity is proved on the actual open overlap, then extended
to its compact-domain boundary by continuity. A single fixed neighborhood
on which derivatives are invertible gives smoothness of the local inverse
to every order. No simultaneous choice of corrections is constructed here. -/
theorem locallySmoothlyConjugate_of_locallySmoothlyExtendable
    {data : FinitePrecompactTopologicalChartAtAtlas3 M}
    {nerve : FiniteAtlasNerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (hlocal : CorrectedTransitionsLocallySmoothlyExtendableOnCompact3
      data nerve correction) :
    CorrectedTransitionsLocallySmoothlyConjugateOnCompact3
      data nerve correction := by
  classical
  obtain ⟨models, hmodels⟩ := exists_finiteLocalSmoothModels_with_correction
    correction correction_neighborhood hlocal
  intro p v hv
  let O : Set E₃ :=
    models.correction p.1.1 '' openOverlapCoordinateImage nerve p
  have hOopen : IsOpen O :=
    (models.correction p.1.1).isOpen_image_of_subset_source
      (isOpen_openOverlapCoordinateImage nerve p)
      (openOverlapCoordinateImage_subset_leftCorrectionSource
        models.correction models.correction_neighborhood p)
  have hvSource : v ∈ (models.correction p.1.1).source :=
    models.correction_neighborhood p.1.1
      (NerveTransitionPackage3.transitionDomain_subset_left_compactCoordinateImage
        nerve p hv)
  have hvClosure : models.correction p.1.1 v ∈ closure O :=
    mem_closure_image ((models.correction p.1.1).continuousAt hvSource)
      (transitionDomain_subset_closure_openOverlapCoordinateImage nerve p hv)
  have hinv : EqOn
      (models.blendedExtension (reversePair nerve p) ∘ models.blendedExtension p)
      id O := by
    rintro _ ⟨w, hw, rfl⟩
    exact blended_reverse_comp_on_compactDomain models p
      (openOverlapCoordinateImage_subset_transitionDomain nerve p hw)
  have hbij : Function.Bijective
      (fderiv ℝ (models.blendedExtension p) (models.correction p.1.1 v)) :=
    smooth_derivative_bijective_at_closure_global hOopen
      (models.blendedExtension_contDiff p)
      (models.blendedExtension_contDiff (reversePair nerve p))
      hvClosure hinv
  obtain ⟨q, hvq, hqf, hq, hqinv⟩ :=
    localDiffeoOfSmooth (models.blendedExtension_contDiff p) hbij
  let e : SmoothLocalDiffeomorphism3 := ⟨q, hq, hqinv⟩
  refine ⟨e, ?_, ?_⟩
  · change correction p.1.1 v ∈ q.source
    simpa only [hmodels] using hvq
  · intro w hw _
    change q (correction p.1.1 w) = correction p.1.2 (nerve.transitionMap p w)
    rw [hqf]
    simpa only [hmodels] using models.blendedExtension_eq_correctedTransition p w hw

end SmoothabilitySmoothGermInvertibilityReduction
end Poincare
