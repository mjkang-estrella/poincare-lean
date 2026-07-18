import Poincare.Global.SmoothabilityAffineGermInvertibilityReduction
import Mathlib.Analysis.Convex.Topology

/-!
# Finite tetrahedral star reduction for three-dimensional smoothability

The remaining finite-nerve smoothability input is a simultaneous family of
vertex corrections for which every corrected transition is locally affine.
A generic piecewise-affine transition does not have that property along its
two-dimensional faces.  This file isolates the precise finite star condition
which removes those kinks without assuming a locally affine germ directly.

Start with a second, developed chart at every vertex of the finite atlas.
The correction from the original preferred coordinates to developed
coordinates is constructed as the transition between those two actual open
partial homeomorphisms.  For each nerve edge, require a finite cover of its
corrected compact domain by closed geometric tetrahedra and a continuous
affine formula on every tetrahedron.

Finiteness and closedness automatically produce, around each corrected
domain point, an open neighborhood meeting only tetrahedra incident to that
point.  The one additional star condition asks that the linear parts of the
affine formulas on incident tetrahedra agree.  Their values at the center
already agree because every formula represents the same corrected
transition there.  `AffineMap.ext_linear` therefore identifies all formulas
in the star, giving one affine germ on the automatically constructed open
neighborhood.

Thus the irreducible PL/Moise theorem is no longer an affine-invertibility
claim or a local-germ claim: it is the construction of developed charts and
a finite tetrahedral presentation whose incident affine pieces have matching
linear parts across every face and lower-dimensional stratum.  A bare PL
triangulation does not imply this matching condition.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityFiniteTetrahedralStarReduction

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

open SmoothabilityFinitePrecompactTopologicalAtlasReduction
open SmoothabilityFiniteAtlasNerveReduction
open SmoothabilityFiniteLocalAffineTransitionModels
open SmoothabilityPLCompatibleAffineConjugacy
open SmoothabilityAffineGermInvertibilityReduction

abbrev PrecompactAtlas3 :=
  FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  FiniteAtlasNerveTransitionPackage3 data

abbrev NerveReduction3 := FiniteAtlasNerveReduction3

/-! ## Corrections constructed from developed PL charts -/

/-- The coordinate correction determined by an original preferred chart and
a developed chart on the same topological space. -/
def vertexCorrectionOfDevelopedCharts
    (data : PrecompactAtlas3 M)
    (developedChart : data.Index → OpenPartialHomeomorph M E₃)
    (i : data.Index) : OpenPartialHomeomorph E₃ E₃ :=
  (data.chart i).symm.trans (developedChart i)

/-- If every developed chart contains the corresponding compact inner-domain
closure, the constructed correction is defined on the whole compact
coordinate image. -/
theorem compactCoordinateImage_subset_vertexCorrectionOfDevelopedCharts_source
    (data : PrecompactAtlas3 M)
    (developedChart : data.Index → OpenPartialHomeomorph M E₃)
    (developedChart_neighborhood : ∀ i,
      closure (data.innerDomain i) ⊆ (developedChart i).source)
    (i : data.Index) :
    data.compactCoordinateImage i ⊆
      (vertexCorrectionOfDevelopedCharts data developedChart i).source := by
  rintro _ ⟨x, hx, rfl⟩
  rw [vertexCorrectionOfDevelopedCharts,
    OpenPartialHomeomorph.trans_source]
  have hxSource : x ∈ (data.chart i).source :=
    data.closure_innerDomain_subset_chart_source i hx
  refine ⟨(data.chart i).map_source hxSource, ?_⟩
  change (data.chart i).symm (data.chart i x) ∈
    (developedChart i).source
  rw [(data.chart i).left_inv hxSource]
  exact developedChart_neighborhood i hx

/-! ## Finite geometric tetrahedral presentation -/

/-- The closed tetrahedron spanned by four vertices in Euclidean
three-space. -/
def tetrahedronCarrier (vertices : Fin 4 → E₃) : Set E₃ :=
  convexHull ℝ (Set.range vertices)

theorem isClosed_tetrahedronCarrier (vertices : Fin 4 → E₃) :
    IsClosed (tetrahedronCarrier vertices) :=
  (Set.finite_range vertices).isClosed_convexHull ℝ

/-- A finite tetrahedral, piecewise-affine presentation of all corrected
compact transitions of one atlas nerve.

This record does not require local affine germs.  Different tetrahedra may
carry different affine formulas, including across a shared face.  The
separate starwise tangent condition below controls precisely that remaining
compatibility. -/
structure FiniteTetrahedralPLTransitionPresentation3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) where
  developedChart : data.Index → OpenPartialHomeomorph M E₃
  developedChart_neighborhood : ∀ i,
    closure (data.innerDomain i) ⊆ (developedChart i).source
  simplexCount : ↑nerve.orderedPairs → ℕ
  simplexVertices : ∀ p, Fin (simplexCount p) → Fin 4 → E₃
  simplex_affineIndependent : ∀ p q,
    AffineIndependent ℝ (simplexVertices p q)
  simplexMap : ∀ p, Fin (simplexCount p) → E₃ →ᴬ[ℝ] E₃
  correctedCompactDomain_subset_simplexCover : ∀ p,
    vertexCorrectionOfDevelopedCharts data developedChart p.1.1 ''
        nerve.transitionDomain p ⊆
      ⋃ q, tetrahedronCarrier (simplexVertices p q)
  simplexMap_agrees_on_correctedCompactDomain :
    ∀ (p : ↑nerve.orderedPairs) (q : Fin (simplexCount p)) (v : E₃),
      v ∈ nerve.transitionDomain p →
      vertexCorrectionOfDevelopedCharts data developedChart p.1.1 v ∈
        tetrahedronCarrier (simplexVertices p q) →
        simplexMap p q
            (vertexCorrectionOfDevelopedCharts data developedChart p.1.1 v) =
          vertexCorrectionOfDevelopedCharts data developedChart p.1.2
            (nerve.transitionMap p v)

namespace FiniteTetrahedralPLTransitionPresentation3

variable {data : PrecompactAtlas3 M}
variable {nerve : NerveTransitionPackage3 data}

/-- The simultaneous correction actually constructed from the developed
charts in the presentation. -/
def correction
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve) :
    data.Index → OpenPartialHomeomorph E₃ E₃ :=
  vertexCorrectionOfDevelopedCharts data input.developedChart

theorem correction_neighborhood
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (i : data.Index) :
    data.compactCoordinateImage i ⊆ (input.correction i).source :=
  compactCoordinateImage_subset_vertexCorrectionOfDevelopedCharts_source
    data input.developedChart input.developedChart_neighborhood i

/-- The geometric carrier of one tetrahedron in the presentation. -/
def simplexCarrier
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (p : ↑nerve.orderedPairs) (q : Fin (input.simplexCount p)) : Set E₃ :=
  tetrahedronCarrier (input.simplexVertices p q)

theorem isClosed_simplexCarrier
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (p : ↑nerve.orderedPairs) (q : Fin (input.simplexCount p)) :
    IsClosed (input.simplexCarrier p q) :=
  isClosed_tetrahedronCarrier (input.simplexVertices p q)

/-- The open neighborhood obtained by deleting every tetrahedron which is
not incident to `y`.  Since the presentation is finite and every tetrahedron
is closed, this is open. -/
def incidentStarNeighborhood
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (p : ↑nerve.orderedPairs) (y : E₃) : Set E₃ :=
  by
    classical
    exact ⋂ q : Fin (input.simplexCount p),
      if y ∈ input.simplexCarrier p q then Set.univ
      else (input.simplexCarrier p q)ᶜ

theorem isOpen_incidentStarNeighborhood
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (p : ↑nerve.orderedPairs) (y : E₃) :
    IsOpen (input.incidentStarNeighborhood p y) := by
  classical
  apply isOpen_iInter_of_finite
  intro q
  by_cases hyq : y ∈ input.simplexCarrier p q
  · simp [hyq]
  · simpa [hyq] using (input.isClosed_simplexCarrier p q).isOpen_compl

theorem center_mem_incidentStarNeighborhood
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (p : ↑nerve.orderedPairs) (y : E₃) :
    y ∈ input.incidentStarNeighborhood p y := by
  classical
  rw [incidentStarNeighborhood, Set.mem_iInter]
  intro q
  by_cases hyq : y ∈ input.simplexCarrier p q
  · simp [hyq]
  · simp [hyq]

/-- Any tetrahedron meeting the incident-star neighborhood is incident to
its center.  This is the finite closed-star localization step. -/
theorem center_mem_simplexCarrier_of_mem_incidentStarNeighborhood
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (p : ↑nerve.orderedPairs) {q : Fin (input.simplexCount p)}
    {y z : E₃}
    (hzStar : z ∈ input.incidentStarNeighborhood p y)
    (hzCarrier : z ∈ input.simplexCarrier p q) :
    y ∈ input.simplexCarrier p q := by
  classical
  by_contra hyCarrier
  have hzAvoid := Set.mem_iInter.1 hzStar q
  simp [hyCarrier] at hzAvoid
  exact hzAvoid hzCarrier

end FiniteTetrahedralPLTransitionPresentation3

/-! ## The exact starwise compatibility left by PL smoothing -/

/-- The affine formulas on any two tetrahedra incident to the same corrected
compact-domain point have equal linear parts.

Only first-order finite star data is asserted.  Equality of the affine maps,
and hence a locally affine transition germ, is derived below from their
common value at the incident point. -/
def StarwiseTangentCompatible3
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve) : Prop :=
  ∀ (p : ↑nerve.orderedPairs) (v : E₃),
    v ∈ nerve.transitionDomain p →
    ∀ (q r : Fin (input.simplexCount p)),
      input.correction p.1.1 v ∈ input.simplexCarrier p q →
      input.correction p.1.1 v ∈ input.simplexCarrier p r →
        (input.simplexMap p q).linear =
          (input.simplexMap p r).linear

/-- Finite closed-star localization plus matching incident linear parts
constructs the exact simultaneous local-affine corrected-transition germs.
-/
theorem correctedTransitionsLocallyAffineOnCompact3_of_tetrahedralStar
    {data : PrecompactAtlas3 M}
    {nerve : NerveTransitionPackage3 data}
    (input : FiniteTetrahedralPLTransitionPresentation3 data nerve)
    (htangent : StarwiseTangentCompatible3 input) :
    CorrectedTransitionsLocallyAffineOnCompact3
      data nerve input.correction := by
  intro p v hv
  have hvCover := input.correctedCompactDomain_subset_simplexCover p
    ⟨v, hv, rfl⟩
  obtain ⟨q₀, hvq₀⟩ := Set.mem_iUnion.1 hvCover
  let y : E₃ := input.correction p.1.1 v
  let U : Set E₃ := input.incidentStarNeighborhood p y
  refine ⟨U, input.isOpen_incidentStarNeighborhood p y,
    input.center_mem_incidentStarNeighborhood p y,
    input.simplexMap p q₀, ?_⟩
  intro w hw hwU
  have hwCover := input.correctedCompactDomain_subset_simplexCover p
    ⟨w, hw, rfl⟩
  obtain ⟨q, hwq⟩ := Set.mem_iUnion.1 hwCover
  have hyq : y ∈ input.simplexCarrier p q :=
    input.center_mem_simplexCarrier_of_mem_incidentStarNeighborhood
      p hwU hwq
  have hlinear : (input.simplexMap p q).linear =
      (input.simplexMap p q₀).linear :=
    htangent p v hv q q₀ hyq hvq₀
  have hcenter : input.simplexMap p q y =
      input.simplexMap p q₀ y := by
    calc
      input.simplexMap p q y =
          input.correction p.1.2 (nerve.transitionMap p v) :=
        input.simplexMap_agrees_on_correctedCompactDomain p q v hv hyq
      _ = input.simplexMap p q₀ y :=
        (input.simplexMap_agrees_on_correctedCompactDomain
          p q₀ v hv hvq₀).symm
  have hmaps : input.simplexMap p q = input.simplexMap p q₀ := by
    apply ContinuousAffineMap.toAffineMap_injective
    exact AffineMap.ext_linear hlinear hcenter
  simpa [hmaps] using
    input.simplexMap_agrees_on_correctedCompactDomain p q w hw hwq

/-- One starwise tangent-compatible tetrahedral presentation constructs the
first nonanalytic field of the strongest finite Poincare boundary. -/
def finiteNervePLCompatibleAffineConjugacy3_of_tetrahedralStar
    (reduction : NerveReduction3 M)
    (input : FiniteTetrahedralPLTransitionPresentation3
      reduction.atlas reduction.transitions)
    (htangent : StarwiseTangentCompatible3 input) :
    FiniteNervePLCompatibleAffineConjugacy3 reduction :=
  finiteNervePLCompatibleAffineConjugacy3_of_locallyAffineOnCompact
    reduction input.correction input.correction_neighborhood
    (correctedTransitionsLocallyAffineOnCompact3_of_tetrahedralStar
      input htangent)

/-- A universal producer of finite developed tetrahedral presentations with
matching incident tangent maps closes the affine-conjugacy provider boundary.
All finite-star neighborhoods, affine-map equalities, invertibility, and
smooth local diffeomorphisms are derived by the verified reductions. -/
theorem plCompatibleAffineConjugacyProvider_of_tetrahedralStarProvider
    (provider : ∀ reduction : NerveReduction3 M,
      ∃ input : FiniteTetrahedralPLTransitionPresentation3
          reduction.atlas reduction.transitions,
        StarwiseTangentCompatible3 input) :
    ∀ reduction : NerveReduction3 M,
      Nonempty (FiniteNervePLCompatibleAffineConjugacy3 reduction) := by
  intro reduction
  obtain ⟨input, htangent⟩ := provider reduction
  exact ⟨finiteNervePLCompatibleAffineConjugacy3_of_tetrahedralStar
    reduction input htangent⟩

end SmoothabilityFiniteTetrahedralStarReduction
end Poincare
