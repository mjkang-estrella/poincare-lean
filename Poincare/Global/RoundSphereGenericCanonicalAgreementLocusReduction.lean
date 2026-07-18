import Poincare.Global.CartanGenericSuccessorDataMovingPersistenceReduction
import Poincare.Global.CartanCanonicalFamilyGermComparison

/-!
# Exact round-target chart-agreement reduction

The legacy round-sphere exponential is a pointwise `Classical.choose` of a
fixed-time local construction.  Its underlying total map includes an
anchor-dependent junk extension outside the honest ODE ball.  The exported
API therefore proves equality with the canonical round-sphere exponential on
a ball at each fixed anchor, but it does not make the full equality locus open
as the anchor moves.

The moving-successor argument does not use global openness of that equality
locus.  It uses only that the zero section lies in its interior.  This module
records the exact locally uniform chart-germ condition equivalent to that
statement and provides recognition-facing wrappers with this strictly weaker
input.

For comparison, the explicit canonical target family is a genuine jointly
regular replacement of the legacy target family at the level of Cartan germs.
Its self-agreement locus is the whole product and hence open.  This is the
honest target-family replacement: no openness claim is made for the opaque
junk-extended legacy equality locus.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000
set_option linter.unusedSectionVars false

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace RoundSphereGenericCanonicalAgreementLocusReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanTargetExponential
open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanGenericSuccessorDataLocalCover
open CartanGenericSuccessorDataMovingPersistenceReduction

/-! ## The exact zero-section condition -/

/-- The target zero section lies in the interior of the existing, explicitly
named generic/canonical chart-agreement locus exactly when the fixed-anchor
chart comparison admits a radius locally uniform in the target anchor.

This is the precise target-side fact used by moving successor persistence.  It
does not ask that accidental equality points of the two total junk-extended
maps away from zero be interior points. -/
theorem zeroSection_subset_interior_genericCanonicalChartAgreementLocus_iff :
    CartanTargetExponential.zeroSection ⊆
        interior genericCanonicalChartAgreementLocus ↔
      ∀ p : RoundSphere3,
        ∃ U : Set RoundSphere3, U ∈ 𝓝 p ∧
          ∃ r > (0 : ℝ), ∀ q ∈ U, ∀ v : E, ‖v‖ < r →
            genericFamily.chart q v = canonicalFamily.chart q v := by
  constructor
  · intro hzero p
    apply
      exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_interior
        p
    apply hzero
    exact ⟨p, Set.mem_univ p, rfl⟩
  · intro hlocal
    rintro _q ⟨p, _hp, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact
      (genericCanonicalChartAgreementLocus_mem_nhds_iff p).mpr
        (hlocal p)

/-- Pointwise form of the preceding equivalence, avoiding the image-set
presentation of the zero section. -/
theorem all_zero_mem_interior_genericCanonicalChartAgreementLocus_iff :
    (∀ p : RoundSphere3,
        (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus) ↔
      ∀ p : RoundSphere3,
        ∃ U : Set RoundSphere3, U ∈ 𝓝 p ∧
          ∃ r > (0 : ℝ), ∀ q ∈ U, ∀ v : E, ‖v‖ < r →
            genericFamily.chart q v = canonicalFamily.chart q v := by
  constructor
  · intro hzero p
    exact
      exists_genericFamily_chart_eq_canonicalFamily_locallyUniform_on_ball_of_mem_interior
        p (hzero p)
  · intro hlocal p
    apply mem_interior_iff_mem_nhds.mpr
    exact
      (genericCanonicalChartAgreementLocus_mem_nhds_iff p).mpr
        (hlocal p)

/-! ## Moving-persistence consumers with no global-openness overstatement -/

section Curvature

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The exact moving-target consumer: local target agreement is requested
only along the complete zero section, and transferred successor packages are
requested only as a neighborhood of the complete parameter diagonal.  No
global openness of either ambient locus is used. -/
theorem localGenericSuccessorDataCover_of_transitionAgreement_of_continuousAtCenters_of_targetZeroInterior_of_packageDiagonalContinuation
    {g : ClosedSmoothRiemannianMetric 3 M}
    (htransition : SubordinateFixedChartTransitionAgreement g)
    (hcontinuous :
      FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M))
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus)
    (hpackage : TransferredSuccessorPackageDiagonalContinuation g) :
    LocalGenericSuccessorDataCover g :=
  (fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_transferredRadiusStability
    (subordinateFixedChartMovingSourceAgreement_of_transitionAgreement_of_continuousAtCenters
      htransition hcontinuous)
    (transferredNormalRadiusLocalStability_of_source_target_package_stability
      hgenericSource htarget hpackage)).toLocalGenericSuccessorDataCover

/-- Subordinate moving-source agreement, generic source stability, and the
exact zero-section interior condition imply the original raw fixed-chart
generic-data persistence contract. -/
theorem fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_targetZeroInterior
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfixedSource : SubordinateFixedChartMovingSourceAgreement g)
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    FixedChartLocalGenericDataPersistence g := by
  apply
    fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_transferredRadiusStability
      hfixedSource
  exact
    transferredNormalRadiusLocalStability_of_source_target_and_isOpen_packageLocus
      hcurv hgenericSource htarget hpackageOpen

/-- Qualitative fixed-chart transition agreement version of the exact
zero-section-interior reduction. -/
theorem fixedChartLocalGenericDataPersistence_of_transitionAgreement_of_continuousAtCenters_of_targetZeroInterior
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (htransition : SubordinateFixedChartTransitionAgreement g)
    (hcontinuous :
      FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M))
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    FixedChartLocalGenericDataPersistence g := by
  apply
    fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_targetZeroInterior
      hcurv
  · exact
      subordinateFixedChartMovingSourceAgreement_of_transitionAgreement_of_continuousAtCenters
        htransition hcontinuous
  · exact hgenericSource
  · exact htarget
  · exact hpackageOpen

/-- The exact target-zero-section condition directly supplies the local
generic successor-data cover used by rooted recognition. -/
theorem localGenericSuccessorDataCover_of_subordinateMovingSource_of_targetZeroInterior
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfixedSource : SubordinateFixedChartMovingSourceAgreement g)
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    LocalGenericSuccessorDataCover g :=
  (fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_targetZeroInterior
    hcurv hfixedSource hgenericSource htarget hpackageOpen).toLocalGenericSuccessorDataCover

/-- Qualitative source-agreement form of the exact local-cover conclusion. -/
theorem localGenericSuccessorDataCover_of_transitionAgreement_of_continuousAtCenters_of_targetZeroInterior
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (htransition : SubordinateFixedChartTransitionAgreement g)
    (hcontinuous :
      FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M))
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htarget : ∀ p : RoundSphere3,
      (p, (0 : E)) ∈ interior genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    LocalGenericSuccessorDataCover g :=
  (fixedChartLocalGenericDataPersistence_of_transitionAgreement_of_continuousAtCenters_of_targetZeroInterior
    hcurv htransition hcontinuous hgenericSource htarget
      hpackageOpen).toLocalGenericSuccessorDataCover

end Curvature

/-! ## The explicit jointly regular target-family replacement -/

/-- The canonical family, viewed as the replacement for the independently
selected legacy generic target family. -/
def canonicalizedGenericFamily : CartanTargetExponential.Family :=
  canonicalFamily

/-- The replacement has the full joint source, target, forward, and inverse
regularity required by supplied-family Cartan continuation. -/
theorem canonicalizedGenericFamily_jointlyRegular :
    canonicalizedGenericFamily.JointlyRegular := by
  simpa [canonicalizedGenericFamily] using canonicalFamily_jointlyRegular

/-- The replacement has the correct identity strict derivative at every
target anchor. -/
theorem canonicalizedGenericFamily_hasIdentityStrictDerivativeAtZero :
    canonicalizedGenericFamily.HasIdentityStrictDerivativeAtZero := by
  simpa [canonicalizedGenericFamily] using
    canonicalFamily_hasIdentityStrictDerivativeAtZero

/-- At each fixed target anchor, replacing the legacy generic family by the
canonicalized family preserves the target chart germ at zero. -/
theorem genericFamily_chart_eventuallyEq_canonicalizedGenericFamily
    (p : RoundSphere3) :
    (genericFamily.chart p : E → E) =ᶠ[𝓝 (0 : E)]
      (canonicalizedGenericFamily.chart p : E → E) := by
  simpa [canonicalizedGenericFamily, genericFamily, canonicalFamily,
    RoundSphereCanonicalExponential.chartOpenPartialHomeomorph,
    GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
    RoundSphereGenericExponentialAnchorIndependence.chart_expAt_eventuallyEq_coordinateLocalHomeomorph
      p

/-- The replacement preserves every legacy Cartan map germ at its source
anchor.  Thus supplied-family continuation may use the jointly regular
replacement without changing the local map consumed by Cartan rigidity. -/
theorem cartanMap_canonicalizedGenericFamily_eventuallyEq_generic
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold I ∞ M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3)
    (L : CartanMap.TangentAlignment g x p) :
    CartanTargetExponential.cartanMap canonicalizedGenericFamily
        g x p L =ᶠ[𝓝 x]
      CartanMap.cartanMap g x p L := by
  simpa [canonicalizedGenericFamily] using
    CartanCanonicalFamilyGermComparison.cartanMap_canonical_eventuallyEq_generic
      g x p L

/-- Joint chart-agreement locus for the explicit replacement and the
canonical family.  Unlike the legacy locus, both displayed families are
definitionally the same jointly regular family. -/
def canonicalizedGenericCanonicalChartAgreementLocus :
    Set (RoundSphere3 × E) :=
  {q | canonicalizedGenericFamily.chart q.1 q.2 =
    canonicalFamily.chart q.1 q.2}

@[simp]
theorem canonicalizedGenericCanonicalChartAgreementLocus_eq_univ :
    canonicalizedGenericCanonicalChartAgreementLocus = Set.univ := by
  ext q
  simp [canonicalizedGenericCanonicalChartAgreementLocus,
    canonicalizedGenericFamily]

/-- The explicit replacement discharges the full open-agreement-locus
condition, not merely its zero-section restriction. -/
theorem isOpen_canonicalizedGenericCanonicalChartAgreementLocus :
    IsOpen canonicalizedGenericCanonicalChartAgreementLocus := by
  rw [canonicalizedGenericCanonicalChartAgreementLocus_eq_univ]
  exact isOpen_univ

/-- Consequently the complete target zero section lies in the interior of
the replacement agreement locus. -/
theorem zeroSection_subset_interior_canonicalizedGenericCanonicalChartAgreementLocus :
    CartanTargetExponential.zeroSection ⊆
      interior canonicalizedGenericCanonicalChartAgreementLocus := by
  rw [canonicalizedGenericCanonicalChartAgreementLocus_eq_univ,
    interior_univ]
  exact Set.subset_univ _

end RoundSphereGenericCanonicalAgreementLocusReduction
end Poincare
