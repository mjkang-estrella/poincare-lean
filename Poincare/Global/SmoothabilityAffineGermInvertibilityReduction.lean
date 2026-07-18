import Poincare.Global.SmoothabilityRawAffineNerveIdentityConjugacy
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local affine corrected germs are automatically invertible

`SmoothabilityFiniteLocalAffineTransitionModels` asks only for continuous
affine maps representing corrected transitions near points of compact overlap
closures.  `SmoothabilityPLCompatibleAffineConjugacy` had strengthened those
local models to continuous affine *equivalences* in order to obtain genuine
local diffeomorphisms.

For the finite atlas nerve occurring here, that strengthening is automatic.
Every compact transition domain contains the image of the actual open chart
overlap, and the whole compact domain lies in the closure of that open image.
Consequently, every open germ
neighborhood appearing in the local-affine condition meets a nonempty open
set on which the affine model agrees with a composition of open partial
homeomorphisms.  The affine model is injective on that open set.  An affine
endomorphism of Euclidean three-space which is injective on a nonempty open
set is globally injective; finite dimensionality then makes it bijective and
its affine inverse continuous.

Thus no separate local-invertibility or determinant hypothesis belongs in
the Moise boundary.  The remaining geometric input is exactly the
simultaneous choice of vertex corrections making every corrected compact
transition locally affine.  This file does not construct those corrections
for an arbitrary topological atlas and does not assert a general Moise or PL
smoothing theorem.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityAffineGermInvertibilityReduction

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

open SmoothabilityFinitePrecompactTopologicalAtlasReduction
open SmoothabilityFiniteAtlasNerveReduction
open SmoothabilityFiniteLocalAffineTransitionModels
open SmoothabilityPLCompatibleAffineConjugacy
open SmoothabilityRawAffineNerveIdentityConjugacy

abbrev PrecompactAtlas3 :=
  FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  FiniteAtlasNerveTransitionPackage3 data

abbrev NerveReduction3 := FiniteAtlasNerveReduction3

/-! ## An affine endomorphism injective on an open set is invertible -/

/-- An affine endomorphism of Euclidean three-space which is injective on one
nonempty open set is globally injective.

The proof is elementary.  If its linear part killed a nonzero vector, a
sufficiently short nonzero multiple of that vector could be added to a point
inside an open ball without changing the affine value, contradicting local
injectivity. -/
theorem continuousAffineMap_injective_of_injOn_nonempty_open
    (A : E₃ →ᴬ[ℝ] E₃) {U : Set E₃}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hAinj : Set.InjOn A U) :
    Function.Injective A := by
  obtain ⟨z, hzU⟩ := hUne
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 hUopen z hzU
  intro x y hxy
  have hlin : A.linear (y - x) = 0 := by
    calc
      A.linear (y - x) = A y - A x :=
        A.toAffineMap.linearMap_vsub y x
      _ = 0 := sub_eq_zero.mpr hxy.symm
  by_contra hxyne
  have hyxne : y ≠ x := fun hyx ↦ hxyne hyx.symm
  have hdpos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyxne)
  let t : ℝ := ε / (2 * ‖y - x‖)
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have htne : t ≠ 0 := ne_of_gt htpos
  have hnorm : ‖t • (y - x)‖ < ε := by
    calc
      ‖t • (y - x)‖ = t * ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      _ = ε / 2 := by
        dsimp [t]
        field_simp [ne_of_gt hdpos]
      _ < ε := by linarith
  have hz' : t • (y - x) + z ∈ U := by
    apply hball
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm
  have hAz : A (t • (y - x) + z) = A z := by
    change A (t • (y - x) +ᵥ z) = A z
    rw [A.map_vadd]
    simp [hlin]
  have hpoint := hAinj hz' hzU hAz
  have hscaled : t • (y - x) = 0 := by
    have := congrArg (fun q : E₃ ↦ q - z) hpoint
    simpa using this
  have hd0 : y - x = 0 := (smul_eq_zero.mp hscaled).resolve_left htne
  exact hxyne (sub_eq_zero.mp hd0).symm

/-- The preceding injectivity result upgrades a continuous affine
endomorphism to a continuous affine equivalence. -/
noncomputable def continuousAffineEquivOfInjOnNonemptyOpen
    (A : E₃ →ᴬ[ℝ] E₃) {U : Set E₃}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hAinj : Set.InjOn A U) :
    E₃ ≃ᴬ[ℝ] E₃ := by
  have hinj : Function.Injective A :=
    continuousAffineMap_injective_of_injOn_nonempty_open A hUopen hUne hAinj
  have hlinearInj : Function.Injective A.linear :=
    A.toAffineMap.linear_injective_iff.mpr hinj
  have hlinearSurj : Function.Surjective A.linear :=
    LinearMap.surjective_of_injective hlinearInj
  have hsurj : Function.Surjective A :=
    A.toAffineMap.linear_surjective_iff.mp hlinearSurj
  let e : E₃ ≃ᵃ[ℝ] E₃ :=
    AffineEquiv.ofBijective ⟨hinj, hsurj⟩
  exact {
    toAffineEquiv := e
    continuous_toFun := e.continuous_of_finiteDimensional
    continuous_invFun := e.symm.continuous_of_finiteDimensional
  }

@[simp]
theorem continuousAffineEquivOfInjOnNonemptyOpen_apply
    (A : E₃ →ᴬ[ℝ] E₃) {U : Set E₃}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hAinj : Set.InjOn A U) (x : E₃) :
    continuousAffineEquivOfInjOnNonemptyOpen A hUopen hUne hAinj x = A x :=
  by
    unfold continuousAffineEquivOfInjOnNonemptyOpen
    change (AffineEquiv.ofBijective _ : E₃ ≃ᵃ[ℝ] E₃) x = A x
    exact AffineEquiv.ofBijective_apply _ x

/-! ## The honest open part of a compact nerve transition -/

/-- The coordinate image of the actual open overlap underlying one compact
nerve transition. -/
def openOverlapCoordinateImage
    {data : PrecompactAtlas3 M}
    (nerve : NerveTransitionPackage3 data)
    (p : ↑nerve.orderedPairs) : Set E₃ :=
  data.chart p.1.1 '' data.overlap p.1.1 p.1.2

theorem isOpen_openOverlapCoordinateImage
    {data : PrecompactAtlas3 M}
    (nerve : NerveTransitionPackage3 data)
    (p : ↑nerve.orderedPairs) :
    IsOpen (openOverlapCoordinateImage nerve p) := by
  apply (data.chart p.1.1).isOpen_image_of_subset_source
  · exact (data.isOpen_innerDomain p.1.1).inter
      (data.isOpen_innerDomain p.1.2)
  · intro x hx
    exact data.innerDomain_subset_chart_source p.1.1 hx.1

theorem openOverlapCoordinateImage_subset_transitionDomain
    {data : PrecompactAtlas3 M}
    (nerve : NerveTransitionPackage3 data)
    (p : ↑nerve.orderedPairs) :
    openOverlapCoordinateImage nerve p ⊆ nerve.transitionDomain p := by
  rw [nerve.transitionDomain_eq p]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, subset_closure hx, rfl⟩

/-- Every point of the compact transition domain lies in the closure of the
coordinate image of the actual open overlap. -/
theorem transitionDomain_subset_closure_openOverlapCoordinateImage
    {data : PrecompactAtlas3 M}
    (nerve : NerveTransitionPackage3 data)
    (p : ↑nerve.orderedPairs) :
    nerve.transitionDomain p ⊆
      closure (openOverlapCoordinateImage nerve p) := by
  rw [nerve.transitionDomain_eq p]
  rintro _ ⟨x, hx, rfl⟩
  exact mem_closure_image ((data.chart p.1.1).continuousAt
    (data.closure_overlap_subset_left_chart_source p.1.1 p.1.2 hx)) hx

theorem openOverlapCoordinateImage_subset_leftCorrectionSource
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (p : ↑nerve.orderedPairs) :
    openOverlapCoordinateImage nerve p ⊆
      (correction p.1.1).source :=
  Subset.trans (openOverlapCoordinateImage_subset_transitionDomain nerve p)
    (Subset.trans
      (NerveTransitionPackage3.transitionDomain_subset_left_compactCoordinateImage
        nerve p)
      (correction_neighborhood p.1.1))

/-! ## Automatic invertibility of corrected local affine germs -/

/-- On the open overlap, the transition followed by the right vertex
correction is injective. -/
theorem injOn_rightCorrectedTransition_on_openOverlap
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (p : ↑nerve.orderedPairs) :
    Set.InjOn
      (fun a ↦ correction p.1.2 (nerve.transitionMap p a))
      (openOverlapCoordinateImage nerve p) := by
  intro a haOpen b hbOpen hab
  have haDomain : a ∈ nerve.transitionDomain p :=
    openOverlapCoordinateImage_subset_transitionDomain nerve p haOpen
  have hbDomain : b ∈ nerve.transitionDomain p :=
    openOverlapCoordinateImage_subset_transitionDomain nerve p hbOpen
  have haRightSource : nerve.transitionMap p a ∈
      (correction p.1.2).source := by
    apply correction_neighborhood p.1.2
    rcases haOpen with ⟨x, hx, rfl⟩
    rw [nerve.transition_agrees_on_overlapClosure p x (subset_closure hx)]
    exact ⟨x, subset_closure hx.2, rfl⟩
  have hbRightSource : nerve.transitionMap p b ∈
      (correction p.1.2).source := by
    apply correction_neighborhood p.1.2
    rcases hbOpen with ⟨x, hx, rfl⟩
    rw [nerve.transition_agrees_on_overlapClosure p x (subset_closure hx)]
    exact ⟨x, subset_closure hx.2, rfl⟩
  have htransition : nerve.transitionMap p a =
      nerve.transitionMap p b :=
    (correction p.1.2).injOn haRightSource hbRightSource hab
  have hab' : a = b :=
    (nerve.transitionMap p).injOn
      (nerve.transitionDomain_subset_source p haDomain)
      (nerve.transitionDomain_subset_source p hbDomain)
      htransition
  exact hab'

/-- The local affine-map condition already implies the local
affine-equivalence condition.  Invertibility is derived from the honest open
overlap inside the compact transition domain. -/
theorem correctedTransitionsLocallyAffineEquivOnCompact3_of_locallyAffineOnCompact
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (hlocal : CorrectedTransitionsLocallyAffineOnCompact3
      data nerve correction) :
    CorrectedTransitionsLocallyAffineEquivOnCompact3
      data nerve correction := by
  intro p v hv
  obtain ⟨U, hUopen, hvU, A, hA⟩ := hlocal p v hv
  let O : Set E₃ := correction p.1.1 '' openOverlapCoordinateImage nerve p
  have hOopen : IsOpen O :=
    (correction p.1.1).isOpen_image_of_subset_source
      (isOpen_openOverlapCoordinateImage nerve p)
      (openOverlapCoordinateImage_subset_leftCorrectionSource
        correction correction_neighborhood p)
  have hvLeftSource : v ∈ (correction p.1.1).source :=
    correction_neighborhood p.1.1
      (NerveTransitionPackage3.transitionDomain_subset_left_compactCoordinateImage
        nerve p hv)
  have hvClosureO : correction p.1.1 v ∈ closure O := by
    exact mem_closure_image ((correction p.1.1).continuousAt hvLeftSource)
      (transitionDomain_subset_closure_openOverlapCoordinateImage nerve p hv)
  have hUO : (U ∩ O).Nonempty :=
    mem_closure_iff.mp hvClosureO U hUopen hvU
  have hUOopen : IsOpen (U ∩ O) := hUopen.inter hOopen
  have hAinj : Set.InjOn A (U ∩ O) := by
    rintro y ⟨hyU, hyO⟩ z ⟨hzU, hzO⟩ hyz
    rcases hyO with ⟨a, haOpen, rfl⟩
    rcases hzO with ⟨b, hbOpen, rfl⟩
    have haDomain : a ∈ nerve.transitionDomain p :=
      openOverlapCoordinateImage_subset_transitionDomain nerve p haOpen
    have hbDomain : b ∈ nerve.transitionDomain p :=
      openOverlapCoordinateImage_subset_transitionDomain nerve p hbOpen
    have hcorrected : correction p.1.2 (nerve.transitionMap p a) =
        correction p.1.2 (nerve.transitionMap p b) := by
      rw [← hA a haDomain hyU, ← hA b hbDomain hzU]
      exact hyz
    have hab : a = b :=
      injOn_rightCorrectedTransition_on_openOverlap
        correction correction_neighborhood p haOpen hbOpen hcorrected
    simp [hab]
  let e : E₃ ≃ᴬ[ℝ] E₃ :=
    continuousAffineEquivOfInjOnNonemptyOpen A hUOopen hUO hAinj
  refine ⟨U, hUopen, hvU, e, ?_⟩
  intro w hw hwU
  simpa [e] using hA w hw hwU

/-- Conversely, forgetting the inverse of each affine equivalence gives the
local affine-map condition. -/
theorem correctedTransitionsLocallyAffineOnCompact3_of_locallyAffineEquivOnCompact
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    {correction : data.Index → OpenPartialHomeomorph E₃ E₃}
    (hlocal : CorrectedTransitionsLocallyAffineEquivOnCompact3
      data nerve correction) :
    CorrectedTransitionsLocallyAffineOnCompact3
      data nerve correction := by
  intro p v hv
  obtain ⟨U, hUopen, hvU, A, hA⟩ := hlocal p v hv
  exact ⟨U, hUopen, hvU, A.toContinuousAffineMap,
    fun w hw hwU ↦ hA w hw hwU⟩

/-- Exact equivalence: for these compact full-dimensional nerve transitions,
local continuous affine maps and local continuous affine equivalences carry
the same geometric content. -/
theorem correctedTransitionsLocallyAffineOnCompact3_iff_affineEquiv
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source) :
    CorrectedTransitionsLocallyAffineOnCompact3 data nerve correction ↔
      CorrectedTransitionsLocallyAffineEquivOnCompact3
        data nerve correction :=
  ⟨correctedTransitionsLocallyAffineEquivOnCompact3_of_locallyAffineOnCompact
      correction correction_neighborhood,
    correctedTransitionsLocallyAffineOnCompact3_of_locallyAffineEquivOnCompact⟩

/-! ## A weaker identity-correction criterion -/

/-- Every raw nerve transition is locally represented on its compact domain
by a continuous affine map.  Unlike the earlier raw criterion, invertibility
of the affine model is not assumed. -/
def RawTransitionsLocallyAffineOnCompact3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) : Prop :=
  ∀ (p : ↑nerve.orderedPairs) (v : E₃),
    v ∈ nerve.transitionDomain p →
      ∃ U : Set E₃,
        IsOpen U ∧
        v ∈ U ∧
        ∃ A : E₃ →ᴬ[ℝ] E₃,
          ∀ w : E₃,
            w ∈ nerve.transitionDomain p →
            w ∈ U →
              A w = nerve.transitionMap p w

/-- With identity vertex corrections, raw local affine-map germs are exactly
the corrected local affine-map germs. -/
theorem correctedTransitionsLocallyAffineOnCompact3_identity_iff_raw
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) :
    CorrectedTransitionsLocallyAffineOnCompact3
        data nerve (identityVertexCorrection data) ↔
      RawTransitionsLocallyAffineOnCompact3 data nerve := by
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

/-- For actual atlas-nerve transitions, even the raw local affine-map
criterion automatically has invertible affine models. -/
theorem rawTransitionsLocallyAffineOnCompact3_iff_affineEquiv
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) :
    RawTransitionsLocallyAffineOnCompact3 data nerve ↔
      RawTransitionsLocallyAffineEquivOnCompact3 data nerve := by
  rw [← correctedTransitionsLocallyAffineOnCompact3_identity_iff_raw,
    ← correctedTransitionsLocallyAffineEquivOnCompact3_identity_iff]
  exact correctedTransitionsLocallyAffineOnCompact3_iff_affineEquiv
    (identityVertexCorrection data)
    (compactCoordinateImage_subset_identityVertexCorrection_source data)

/-! ## Producers for the finite-nerve boundary -/

/-- The weaker local affine-map germ data directly constructs the
PL-compatible affine-conjugacy package. -/
def finiteNervePLCompatibleAffineConjugacy3_of_locallyAffineOnCompact
    (reduction : NerveReduction3 M)
    (correction : reduction.atlas.Index →
      OpenPartialHomeomorph E₃ E₃)
    (correction_neighborhood : ∀ i,
      reduction.atlas.compactCoordinateImage i ⊆
        (correction i).source)
    (hlocal : CorrectedTransitionsLocallyAffineOnCompact3
      reduction.atlas reduction.transitions correction) :
    FiniteNervePLCompatibleAffineConjugacy3 reduction where
  correction := correction
  correction_neighborhood := correction_neighborhood
  local_affine_equiv :=
    correctedTransitionsLocallyAffineEquivOnCompact3_of_locallyAffineOnCompact
      correction correction_neighborhood hlocal

/-- An already locally affine raw finite nerve produces the affine-conjugacy
field using identity vertex corrections.  The local affine maps need not be
presented as equivalences. -/
def finiteNervePLCompatibleAffineConjugacy3_of_rawTransitionsLocallyAffine
    (reduction : NerveReduction3 M)
    (hraw : RawTransitionsLocallyAffineOnCompact3
      reduction.atlas reduction.transitions) :
    FiniteNervePLCompatibleAffineConjugacy3 reduction :=
  finiteNervePLCompatibleAffineConjugacy3_of_locallyAffineOnCompact
    reduction (identityVertexCorrection reduction.atlas)
    (compactCoordinateImage_subset_identityVertexCorrection_source
      reduction.atlas)
    ((correctedTransitionsLocallyAffineOnCompact3_identity_iff_raw
      reduction.atlas reduction.transitions).2 hraw)

/-- In particular, the pre-existing finite local-affine transition-model
record constructs the stronger affine-conjugacy package; no invertibility
field is needed. -/
def finiteNervePLCompatibleAffineConjugacy3_of_finiteLocalAffineTransitionModels3
    (reduction : NerveReduction3 M)
    (models : FiniteLocalAffineTransitionModels3
      reduction.atlas reduction.transitions) :
    FiniteNervePLCompatibleAffineConjugacy3 reduction :=
  finiteNervePLCompatibleAffineConjugacy3_of_locallyAffineOnCompact
    reduction models.correction models.correction_neighborhood
    (correctedTransitionsLocallyAffineOnCompact3_of_finiteModels models)

/-- Exact finite-nerve boundary equivalence.  Requiring affine
*equivalences* contributes no geometric hypothesis beyond the earlier finite
local affine-map models. -/
theorem nonempty_finiteNervePLCompatibleAffineConjugacy3_iff_finiteLocalAffineTransitionModels3
    (reduction : NerveReduction3 M) :
    Nonempty (FiniteNervePLCompatibleAffineConjugacy3 reduction) ↔
      Nonempty (FiniteLocalAffineTransitionModels3
        reduction.atlas reduction.transitions) := by
  constructor
  · rintro ⟨input⟩
    obtain ⟨models⟩ := input.finiteModels
    exact ⟨models.toFiniteLocalAffineTransitionModels3⟩
  · rintro ⟨models⟩
    exact ⟨finiteNervePLCompatibleAffineConjugacy3_of_finiteLocalAffineTransitionModels3
      reduction models⟩

/-- Pointwise local affine-map germs are therefore an exact, finitary-choice
free statement of the remaining smoothability input for one finite nerve. -/
theorem nonempty_finiteNervePLCompatibleAffineConjugacy3_iff_exists_localAffineGerms
    (reduction : NerveReduction3 M) :
    Nonempty (FiniteNervePLCompatibleAffineConjugacy3 reduction) ↔
      ∃ correction : reduction.atlas.Index →
          OpenPartialHomeomorph E₃ E₃,
        (∀ i, reduction.atlas.compactCoordinateImage i ⊆
          (correction i).source) ∧
        CorrectedTransitionsLocallyAffineOnCompact3
          reduction.atlas reduction.transitions correction := by
  rw [nonempty_finiteNervePLCompatibleAffineConjugacy3_iff_finiteLocalAffineTransitionModels3]
  exact nonempty_finiteLocalAffineTransitionModels3_iff_exists_localGerms

/-- At the universal level, affine-conjugacy providers and finite local
affine-map providers are equivalent. -/
theorem universal_plCompatibleAffineConjugacyProvider_iff_finiteLocalAffineTransitionModelsProvider
    : (∀ reduction : NerveReduction3 M,
        Nonempty (FiniteNervePLCompatibleAffineConjugacy3 reduction)) ↔
      (∀ reduction : NerveReduction3 M,
        Nonempty (FiniteLocalAffineTransitionModels3
          reduction.atlas reduction.transitions)) := by
  constructor
  · intro provider reduction
    exact
      (nonempty_finiteNervePLCompatibleAffineConjugacy3_iff_finiteLocalAffineTransitionModels3
        reduction).mp (provider reduction)
  · intro provider reduction
    exact
      (nonempty_finiteNervePLCompatibleAffineConjugacy3_iff_finiteLocalAffineTransitionModels3
        reduction).mpr (provider reduction)

/-- Therefore any provider for the genuinely weaker local affine-map germs
supplies the first smoothability field used by the strongest finite boundary. -/
theorem plCompatibleAffineConjugacyProvider_of_localAffineGermProvider
    (provider : ∀ reduction : NerveReduction3 M,
      ∃ correction : reduction.atlas.Index →
          OpenPartialHomeomorph E₃ E₃,
        (∀ i, reduction.atlas.compactCoordinateImage i ⊆
          (correction i).source) ∧
        CorrectedTransitionsLocallyAffineOnCompact3
          reduction.atlas reduction.transitions correction) :
    ∀ reduction : NerveReduction3 M,
      Nonempty (FiniteNervePLCompatibleAffineConjugacy3 reduction) := by
  intro reduction
  obtain ⟨correction, hneighborhood, hlocal⟩ := provider reduction
  exact ⟨finiteNervePLCompatibleAffineConjugacy3_of_locallyAffineOnCompact
    reduction correction hneighborhood hlocal⟩

end SmoothabilityAffineGermInvertibilityReduction
end Poincare
