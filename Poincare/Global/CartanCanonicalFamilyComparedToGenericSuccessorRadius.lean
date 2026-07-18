import Poincare.Global.CartanCanonicalFamilyProvenanceRootedAssembly
import Poincare.Global.CartanAtlasRootedPathCurvatureSuccessorRadius

/-!
# Forgetting canonical-family provenance to a generic successor radius

The provenance-retaining canonical successor locus is stronger than the
generic differential-successor locus.  Its comparison field contains an
actual generic datum, but that datum is indexed by the generic state obtained
by forgetting the canonical-family tag.  This module records the elementary
dependent reindexing needed to use that datum for an arbitrary legacy
`CartanChain.ChainState`.

Consequently, a neighborhood of the parameter diagonal in the compared locus
gives both the existing generic `UniversalSuccessorDataNeighborhood` and one
positive radius valid for every generic state.  The latter is exactly the
successor-data input used by the reparameterized-grid realization.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanCanonicalFamilyComparedToGenericSuccessorRadius

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanCanonicalFamilyGermComparison
open CartanCanonicalFamilySuccessorProvenance
open CartanCanonicalFamilyProvenanceRootedAssembly

/-- Equip a legacy generic state with the canonical target-family tag while
leaving its anchor, target, and alignment unchanged. -/
def canonicalStateOfGeneric
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) : ChainState canonicalFamily g where
  anchor := s.anchor
  target := s.target
  alignment := s.alignment

/-- Forgetting the tag from the rebuilt canonical state recovers the original
generic state, including its dependent tangent alignment. -/
@[simp]
theorem canonicalToGenericState_canonicalStateOfGeneric
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) :
    canonicalToGenericState (canonicalStateOfGeneric s) = s := by
  cases s
  rfl

/-- The comparison retained by a canonical step contains a generic
differential-successor datum for the original legacy state. -/
def genericDataOfCanonicalComparedStep
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (step : CanonicalComparedStep (canonicalStateOfGeneric s) z) :
    DifferentialInducedSuccessor.Data s z := by
  simpa only [canonicalToGenericState_canonicalStateOfGeneric] using
    step.comparison.genericData

/-- The canonical state formed from the fields of a structure constructor is
definitionally the corresponding canonical-family constructor. -/
@[simp]
theorem canonicalStateOfGeneric_mk
    {g : ClosedSmoothRiemannianMetric 3 M}
    (x : M) (p : RoundSphere3)
    (L : CartanMap.TangentAlignment g x p) :
    canonicalStateOfGeneric (CartanChain.ChainState.mk x p L) =
      (ChainState.mk x p L : ChainState canonicalFamily g) :=
  rfl

/-- Every point carrying a canonical successor together with its comparison
also carries ordinary generic differential-successor data. -/
theorem universalComparedSuccessorLocus_subset_universalSuccessorDataLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    UniversalComparedSuccessorLocus g ⊆
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
        g := by
  rintro ⟨⟨x, p⟩, z⟩ hcompared L
  let s : CartanChain.ChainState g := CartanChain.ChainState.mk x p L
  have hstep :
      Nonempty (CanonicalComparedStep (canonicalStateOfGeneric s) z) := by
    simpa only [s, canonicalStateOfGeneric_mk] using hcompared L
  rcases hstep with ⟨step⟩
  exact ⟨genericDataOfCanonicalComparedStep step⟩

/-- The two independently named parameter diagonals are the same subset of
the common source-target-next parameter space. -/
theorem targetExponential_successorParameterDiagonal_eq_generic
    (M : Type u) [TopologicalSpace M] :
    CartanTargetExponential.successorParameterDiagonal (M := M) =
      CartanAtlasRootedPathCurvatureSuccessorRadius.successorParameterDiagonal
        (M := M) :=
  rfl

section Compact

variable [CompactSpace M] [ConnectedSpace M]

/-- The compared canonical neighborhood is already the generic joint
successor-data neighborhood after forgetting its additional provenance. -/
theorem universalSuccessorDataNeighborhood_of_comparedNeighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hneighborhood : UniversalComparedSuccessorLocus g ∈
      nhdsSet
        (CartanTargetExponential.successorParameterDiagonal (M := M))) :
    CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood
      g := by
  rw [CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood]
  rw [← targetExponential_successorParameterDiagonal_eq_generic M]
  exact Filter.mem_of_superset hneighborhood
    (universalComparedSuccessorLocus_subset_universalSuccessorDataLocus g)

/-- A radius supplying compared canonical steps for all triples supplies
ordinary differential data for every arbitrary generic Cartan state. -/
theorem uniformGenericSuccessorData_of_uniformComparedRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    {rho : ℝ}
    (hcompared :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < rho →
          Nonempty (CanonicalComparedStep (ChainState.mk x p L) z)) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ (s : CartanChain.ChainState g) (z : M),
      dist z s.anchor < rho →
        Nonempty (DifferentialInducedSuccessor.Data s z) := by
  letI : MetricSpace M := g.toMetricSpace
  intro s z hdist
  have hstep :
      Nonempty (CanonicalComparedStep (canonicalStateOfGeneric s) z) := by
    simpa only [canonicalStateOfGeneric] using
      hcompared s.anchor s.target s.alignment z hdist
  rcases hstep with ⟨step⟩
  exact ⟨genericDataOfCanonicalComparedStep step⟩

/-- Compact uniformization of a compared neighborhood yields one positive
radius valid for every arbitrary generic state.  The final quantified clause
is exactly the `hdata` contract of
`CartanRootedOverlapReparameterizedGridRealization.realizedGrid_of_uniformSuccessorRadius`.
-/
theorem exists_uniform_genericSuccessorData_radius_of_comparedNeighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hneighborhood : UniversalComparedSuccessorLocus g ∈
      nhdsSet
        (CartanTargetExponential.successorParameterDiagonal (M := M))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ rho > (0 : ℝ),
      ∀ (s : CartanChain.ChainState g) (z : M),
        dist z s.anchor < rho →
          Nonempty (DifferentialInducedSuccessor.Data s z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_comparedSuccessor_radius hneighborhood with
    ⟨rho, hrho, hcompared⟩
  exact ⟨rho, hrho,
    uniformGenericSuccessorData_of_uniformComparedRadius hcompared⟩

end Compact

end CartanCanonicalFamilyComparedToGenericSuccessorRadius
end Poincare
