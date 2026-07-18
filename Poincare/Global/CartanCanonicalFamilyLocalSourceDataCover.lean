import Poincare.Global.CartanCanonicalFamilyComparedCanonicalContinuation

/-!
# Exact local-source cover for canonical Cartan data

The canonical continuation route previously exposed two independent pieces of
proof data:

* `GenericNormalControlledLocalFamilyCover`, comparing a chart-local normal
  family with the independently chosen preferred generic exponential; and
* `LocallyUniformCanonicalRadiusEnvelope`, a globally selected positive lower
  semicontinuous family of admissible generic-normal radii.

Their consumer retains neither object.  It only uses them to construct, near
each source anchor, one open jointly continuous local normal family whose
small controlled successor locus is contained in the canonical supplied-data
locus.  This file records that exact combined output as
`CanonicalLocalSourceDataCover`.

The fixed-chart parameterized inverse-function construction already supplies
the required open local family, without transporting its inverse velocity to
the preferred chart at the moving anchor.  Consequently the narrowest
fixed-chart residual is just a controlled-locus inclusion for the raw product
inverse.  `FixedChartCanonicalDataPersistence` states precisely that
inclusion.  It mentions no preferred-chart transition, no generic-normal
continuity, and no lower-semicontinuous radius selection.

Pointwise constant-curvature data do not prove this residual: their positive
radius may depend independently on both the moving source anchor and the
sphere target.  The fixed-chart inverse controls the source endpoint jointly,
but it does not by itself make those target-uniform data radii persist.  That
remaining quantifier is kept explicit here.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000
set_option linter.unusedSectionVars false

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyLocalSourceDataCover

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport
open CartanCanonicalFamilyComparedForwardNormalRegularity
open CartanCanonicalFamilyComparedCanonicalContinuation
open CartanCanonicalFamilyLocalUniformData

section ExactCover

/--
The exact chart-local output used to prove the canonical supplied-family
successor neighborhood.

All source-family regularity is stored in `LocalFamily`; all remaining
mathematics is the actual `LocalUniformNormalSuccessorData` conclusion.  In
particular this contract stores neither a comparison with `genericFamily` nor
a radius function on `M × RoundSphere3`.
-/
def CanonicalLocalSourceDataCover
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ A : LocalFamily g,
      x₀ ∈ A.anchors ∧ LocalUniformNormalSuccessorData A canonicalFamily

/-- Locus-inclusion characterization of the exact local cover. -/
theorem canonicalLocalSourceDataCover_iff_controlledLocusCover
    (g : ClosedSmoothRiemannianMetric 3 M) :
    CanonicalLocalSourceDataCover g ↔
      ∀ x₀ : M,
        ∃ A : LocalFamily g, x₀ ∈ A.anchors ∧
          ∃ radius > (0 : ℝ),
            A.controlledSuccessorLocus radius ⊆
              UniversalSuccessorDataLocus canonicalFamily g := by
  constructor
  · intro hcover x₀
    rcases hcover x₀ with ⟨A, hx₀A, hdata⟩
    rcases
        (localUniformNormalSuccessorData_iff_controlledLocus_subset
          A canonicalFamily).mp hdata with
      ⟨radius, hradius, hsubset⟩
    exact ⟨A, hx₀A, radius, hradius, hsubset⟩
  · intro hcover x₀
    rcases hcover x₀ with
      ⟨A, hx₀A, radius, hradius, hsubset⟩
    refine ⟨A, hx₀A, ?_⟩
    exact
      (localUniformNormalSuccessorData_iff_controlledLocus_subset
        A canonicalFamily).mpr ⟨radius, hradius, hsubset⟩

/-- The exact local cover is sufficient for the global diagonal
neighborhood. -/
theorem CanonicalLocalSourceDataCover.toUniversalSuccessorDataNeighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcover : CanonicalLocalSourceDataCover g) :
    UniversalSuccessorDataNeighborhood canonicalFamily g := by
  exact universalSuccessorDataNeighborhood_of_localSourceFamilyCover
    canonicalFamily hcover

end ExactCover

section FixedChart

/--
The exact residual after the fixed-chart parameterized inverse theorem.

The package already contains an open anchor set, an open joint endpoint locus,
and a jointly continuous raw inverse velocity.  The only requested fact is
that some positive controlled locus of this concrete raw family consists of
actual canonical successor data, uniformly over all target anchors and
alignments.
-/
def FixedChartCanonicalDataPersistence
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      ∃ radius > (0 : ℝ),
        C.rawLocalFamily.controlledSuccessorLocus radius ⊆
          UniversalSuccessorDataLocus canonicalFamily g

/-- The fixed-chart inverse-function theorem supplies the local family and
its center-anchor membership unconditionally. -/
theorem exists_rawFixedChartLocalFamily
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      x₀ ∈ C.rawLocalFamily.anchors := by
  rcases exists_fixedChartAnchorEndpointPackage g x₀ with ⟨C⟩
  exact ⟨C, C.center_mem_rawLocalFamily_anchors⟩

/-- Fixed-chart canonical-data persistence gives the exact local source
cover, with no preferred-chart velocity transport. -/
theorem FixedChartCanonicalDataPersistence.toCanonicalLocalSourceDataCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hfixed : FixedChartCanonicalDataPersistence g) :
    CanonicalLocalSourceDataCover g := by
  rw [canonicalLocalSourceDataCover_iff_controlledLocusCover]
  intro x₀
  rcases hfixed x₀ with ⟨C, radius, hradius, hsubset⟩
  exact ⟨C.rawLocalFamily, C.center_mem_rawLocalFamily_anchors,
    radius, hradius, hsubset⟩

/-- Direct global-neighborhood consumer for the fixed-chart residual. -/
theorem universalSuccessorDataNeighborhood_of_fixedChartCanonicalDataPersistence
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hfixed : FixedChartCanonicalDataPersistence g) :
    UniversalSuccessorDataNeighborhood canonicalFamily g :=
  hfixed.toCanonicalLocalSourceDataCover.toUniversalSuccessorDataNeighborhood

end FixedChart

section PreviousSplitInputs

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/--
The former split source-control/radius-envelope inputs imply the exact local
source-data cover.  This one-way projection demonstrates what their consumer
actually retains.
-/
theorem canonicalLocalSourceDataCover_of_controlledLocalFamilyCover_of_radiusEnvelope
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (R : LocallyUniformCanonicalRadiusEnvelope g) :
    CanonicalLocalSourceDataCover g := by
  intro x₀
  rcases
      exists_chartLocal_genericNormal_canonicalData_of_radiusEnvelope R x₀ with
    ⟨U, hU, hx₀U, genericRadius, hgenericRadius, hgenericData⟩
  rcases hcontrol x₀ genericRadius hgenericRadius with
    ⟨A, hx₀A, localRadius, hlocalRadius, hcontrols⟩
  let B : LocalFamily g := A.restrictAnchors U hU
  have hx₀B : x₀ ∈ B.anchors := ⟨hx₀A, hx₀U⟩
  have hcontrolsB : B.ControlsGenericNormal localRadius genericRadius := by
    intro x z hzSource hzNorm
    exact hcontrols x z hzSource.1 hzNorm
  have hdataB : LocalUniformNormalSuccessorData B canonicalFamily := by
    apply localUniformNormalSuccessorData_of_controlsGenericNormal
      B canonicalFamily hlocalRadius hcontrolsB
    intro x hx p L z hzSource hzNorm
    exact hgenericData x hx.2 p L z hzSource hzNorm
  exact ⟨B, hx₀B, hdataB⟩

/-- Curvature/minorant form projected directly to the exact local cover. -/
theorem canonicalLocalSourceDataCover_of_curvature_of_controlledLocalFamilyCover_of_jointMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalNormalAnchorTargetRadius hcurv x p) :
    CanonicalLocalSourceDataCover g := by
  exact
    canonicalLocalSourceDataCover_of_controlledLocalFamilyCover_of_radiusEnvelope
      hcontrol
      (canonicalRadiusEnvelope_of_jointMinorant hcurv pairRadius
        hpositive hlower hminorant)

end PreviousSplitInputs

section Recognition

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/--
Recognition-facing form of the reduction.  The two former source-control and
radius-envelope fields are replaced by their exact local canonical-data
output.  The independent canonical-to-compared and equality-persistence
boundaries remain unchanged.
-/
theorem unitConstantCurvatureSphereRecognition3_of_localSourceDataCover_of_continuation_localPersistentActualSuccessorEqualityRadius
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (localData : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalLocalSourceDataCover g)
    (comparisonContinuation : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalComparedDiagonalContinuation g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalNeighborhood_of_continuation_uniformActualSuccessorEquality
  · intro g hcurv
    exact
      (localData g hcurv).toUniversalSuccessorDataNeighborhood
  · exact comparisonContinuation
  · intro g hcurv
    exact
      DifferentialSuccessorEqualityStabilityReduction.uniformActualSuccessorEquality_of_localPersistence
        g (equalityStability g hcurv)

/-- Fixed-chart specialization of the exact recognition-facing reduction. -/
theorem unitConstantCurvatureSphereRecognition3_of_fixedChartCanonicalDataPersistence_of_continuation_localPersistentActualSuccessorEqualityRadius
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (fixedChartData : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        FixedChartCanonicalDataPersistence g)
    (comparisonContinuation : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalComparedDiagonalContinuation g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_localSourceDataCover_of_continuation_localPersistentActualSuccessorEqualityRadius
  · intro g hcurv
    exact
      (fixedChartData g hcurv).toCanonicalLocalSourceDataCover
  · exact comparisonContinuation
  · exact equalityStability

end Recognition

end CartanCanonicalFamilyLocalSourceDataCover
end Poincare
