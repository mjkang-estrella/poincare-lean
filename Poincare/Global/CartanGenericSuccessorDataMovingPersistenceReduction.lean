import Poincare.Global.CartanGenericSuccessorDataLocalCover
import Poincare.Global.CartanCanonicalFamilyProvenanceLocalUniformData

/-!
# Moving-anchor reduction for fixed-chart generic successor data

The fixed-chart inverse-function package has a jointly continuous raw inverse
velocity, but the public source and target exponential charts are selected
independently at every anchor.  Fixed-anchor ODE uniqueness therefore does not
by itself give a radius which persists when either anchor moves.

This file separates that remaining issue into concrete moving-parameter
statements and proves that they imply the original raw
`FixedChartLocalGenericDataPersistence` contract.

The source-side input asks for a fixed-chart package subordinate to an
arbitrary neighborhood of its center, together with

* the existing positive-time endpoint comparison with the public exponential;
* joint continuity of the transported inverse velocity; and
* a uniform operator-norm bound for the fixed-chart-to-preferred-chart
  transition derivative on the retained anchors.

The second theorem reduces the remaining generic-normal data stability to the
already isolated open loci: generic/canonical target-chart germ agreement and
conditional transferred-package continuation.  Thus the conclusion is the
original raw fixed-chart contract, not a renamed local-cover premise.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanGenericSuccessorDataMovingPersistenceReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport
open CartanGenericSuccessorDataLocalCover
open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalFamilySuccessorProvenance
open CartanCanonicalFamilyProvenanceLocalUniformData

/-! ## Concrete moving-source input -/

/-- The fixed-chart-to-preferred-chart transition derivative, with both the
frozen center and the varying preferred-chart anchor displayed. -/
def fixedToPreferredTransitionDerivative (x₀ x : M) : E →L[ℝ] E :=
  GeodesicTransport.chartTransitionDeriv x₀ x
    (extChartAt I x₀ x)

/-- At the frozen-chart center the fixed-to-preferred transition derivative
is the identity. -/
@[simp]
theorem fixedToPreferredTransitionDerivative_self (x : M) :
    fixedToPreferredTransitionDerivative x x =
      ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  simpa [fixedToPreferredTransitionDerivative,
    CartanSourceExponentialLocalFamilyTransport.fixedToAnchorVelocity] using
    CartanSourceExponentialLocalFamilyTransport.fixedToAnchorVelocity_self
      x v

/--
The narrow operator-valued continuity statement which makes the
fixed-to-preferred transition derivative locally bounded.

All ordinary chart-transition regularity theorems keep both chart anchors
fixed.  Here the preferred-chart anchor varies, so this is precisely the
continuity not included in the bare `ChartedSpace.chartAt` selection API.
-/
def FixedToPreferredTransitionDerivativeContinuousAtCenters : Prop :=
  ∀ x₀ : M,
    ContinuousAt (fixedToPreferredTransitionDerivative x₀) x₀

/-- Continuity at a frozen center supplies a positive local operator-norm
bound for the fixed-to-preferred transition derivative. -/
theorem exists_local_fixedToPreferredTransitionDerivative_bound_of_continuousAtCenters
    (hcontinuous :
      FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M))
    (x₀ : M) :
    ∃ U : Set M, U ∈ 𝓝 x₀ ∧
      ∃ K > (0 : ℝ),
        ∀ x ∈ U, ‖fixedToPreferredTransitionDerivative x₀ x‖ ≤ K := by
  let D : M → E →L[ℝ] E := fixedToPreferredTransitionDerivative x₀
  let K : ℝ := ‖D x₀‖ + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hDcontinuous : ContinuousAt D x₀ := by
    simpa only [D] using hcontinuous x₀
  have hnormContinuous : ContinuousAt (fun x : M ↦ ‖D x‖) x₀ :=
    (@continuous_norm (E →L[ℝ] E) _).continuousAt.comp hDcontinuous
  let U : Set M := {x | ‖D x‖ < K}
  have hU : U ∈ 𝓝 x₀ := by
    change (fun x : M ↦ ‖D x‖) ⁻¹' Iio K ∈ 𝓝 x₀
    apply hnormContinuous.preimage_mem_nhds
    exact Iio_mem_nhds (by dsimp only [K]; linarith)
  refine ⟨U, hU, K, hK, ?_⟩
  intro x hx
  exact le_of_lt hx

/--
The positive-time fixed-chart ODE agreement, localized inside an arbitrary
source neighborhood.  Unlike the stronger structure below, this premise asks
for no quantitative derivative bound and contains no successor datum.
-/
def SubordinateFixedChartTransitionAgreement
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (U : Set M), U ∈ 𝓝 x₀ →
    ∃ (C : FixedChartAnchorEndpointPackage g x₀)
        (P : C.TransitionAgreementPackage),
      C.rawLocalFamily.anchors ⊆ U

/--
The fixed-chart source construction, subordinate to any prescribed
neighborhood of its center.

`TransitionAgreementPackage` is the existing proof-bearing output of the
parameterized geodesic/ODE construction: it contains joint continuity of the
transported inverse and positive-time endpoint agreement with the public
varying-anchor exponential.  The additional operator bound is exactly what
converts a small *raw fixed-chart* inverse velocity into a uniformly small
preferred-anchor velocity.

Requiring the retained anchor set to lie in the supplied neighborhood is a
localization condition, not successor-data persistence: the structure
mentions no Cartan successor datum.
-/
def SubordinateFixedChartMovingSourceAgreement
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (U : Set M), U ∈ 𝓝 x₀ →
    ∃ (C : FixedChartAnchorEndpointPackage g x₀)
        (P : C.TransitionAgreementPackage),
      C.rawLocalFamily.anchors ⊆ U ∧
        ∃ K > (0 : ℝ),
          ∀ x ∈ C.rawLocalFamily.anchors,
            ‖GeodesicTransport.chartTransitionDeriv x₀ x
                (extChartAt I x₀ x)‖ ≤ K

/-- The qualitative subordinate ODE agreement plus continuity of the moving
transition derivative gives the quantitative moving-source package. -/
theorem subordinateFixedChartMovingSourceAgreement_of_transitionAgreement_of_continuousAtCenters
    {g : ClosedSmoothRiemannianMetric 3 M}
    (htransition : SubordinateFixedChartTransitionAgreement g)
    (hcontinuous :
      FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M)) :
    SubordinateFixedChartMovingSourceAgreement g := by
  intro x₀ U hU
  rcases
      exists_local_fixedToPreferredTransitionDerivative_bound_of_continuousAtCenters
        hcontinuous x₀ with
    ⟨V, hV, K, hK, hbound⟩
  rcases htransition x₀ (U ∩ V) (inter_mem hU hV) with
    ⟨C, P, hanchors⟩
  refine ⟨C, P, fun x hx ↦ (hanchors hx).1, K, hK, ?_⟩
  intro x hx
  have hxV : x ∈ V := (hanchors hx).2
  simpa [fixedToPreferredTransitionDerivative] using hbound x hxV

/-! ## Raw-to-generic normal control -/

/--
On a source package with a uniform transition-derivative bound, a raw normal
ball maps into any prescribed transported-normal ball.  This is the analytic
estimate which lets the conclusion retain `C.rawLocalFamily`, rather than
silently replacing it by the transported family.
-/
theorem rawNormal_controls_transportedNormal
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {K targetRadius : ℝ}
    (hK : 0 < K)
    (hbound : ∀ x ∈ C.rawLocalFamily.anchors,
      ‖GeodesicTransport.chartTransitionDeriv x₀ x
          (extChartAt I x₀ x)‖ ≤ K)
    {x z : M}
    (hzSource : (x, z) ∈ C.rawLocalFamily.sourceLocus)
    (hzNorm : ‖C.rawLocalFamily.normal (x, z)‖ < targetRadius / K) :
    ‖C.transportedNormal (x, z)‖ < targetRadius := by
  let D : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionDeriv x₀ x
      (extChartAt I x₀ x)
  have hxAnchor : x ∈ C.rawLocalFamily.anchors :=
    C.rawLocalFamily.sourceLocus_fst (x, z) hzSource
  have hD : ‖D‖ ≤ K := by
    simpa [D] using hbound x hxAnchor
  calc
    ‖C.transportedNormal (x, z)‖ =
        ‖D (C.rawLocalFamily.normal (x, z))‖ := rfl
    _ ≤ ‖D‖ * ‖C.rawLocalFamily.normal (x, z)‖ :=
      D.le_opNorm _
    _ ≤ K * ‖C.rawLocalFamily.normal (x, z)‖ := by
      exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)
    _ < K * (targetRadius / K) :=
      mul_lt_mul_of_pos_left hzNorm hK
    _ = targetRadius := by
      exact mul_div_cancel₀ targetRadius (ne_of_gt hK)

set_option maxHeartbeats 2000000 in
/-- A single quantitative fixed-chart package and a target-local family of
admissible generic-normal radii give the required raw controlled-locus
inclusion.  This helper keeps the dependent endpoint-agreement calculation
out of the neighborhood-selection theorem below. -/
theorem controlledRawFixedChartLocus_subset_universalGenericData
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    (P : C.TransitionAgreementPackage)
    (targets : Set RoundSphere3)
    {genericRadius K : ℝ}
    (hK : 0 < K)
    (hbound : ∀ x ∈ C.rawLocalFamily.anchors,
      ‖fixedToPreferredTransitionDerivative x₀ x‖ ≤ K)
    (hadmissible : ∀ x ∈ C.rawLocalFamily.anchors,
      ∀ p ∈ targets,
        TransferredNormalRadiusAdmissible g x p genericRadius) :
    controlledGenericSuccessorLocusOn C.rawLocalFamily targets
        (min P.radius genericRadius / K) ⊆
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
        g := by
  rintro ⟨⟨x, p⟩, z⟩ hcontrolled L
  have hzRaw : (x, z) ∈ C.rawLocalFamily.sourceLocus :=
    hcontrolled.1.1
  have hzRawNorm :
      ‖C.rawLocalFamily.normal (x, z)‖ <
        min P.radius genericRadius / K := by
    simpa [LocalFamily.controlledSourceLocus, Metric.mem_ball,
      dist_eq_norm] using hcontrolled.1.2
  have htransportedNorm :
      ‖C.transportedNormal (x, z)‖ < min P.radius genericRadius := by
    apply rawNormal_controls_transportedNormal C hK
    · intro y hy
      simpa [fixedToPreferredTransitionDerivative] using hbound y hy
    · exact hzRaw
    · exact hzRawNorm
  have htransportedEndpointNorm :
      ‖C.transportedNormal (x, z)‖ < P.radius :=
    htransportedNorm.trans_le (min_le_left _ _)
  have htransportedGenericNorm :
      ‖C.transportedNormal (x, z)‖ < genericRadius :=
    htransportedNorm.trans_le (min_le_right _ _)
  let A : LocalFamily g := C.transportedLocalFamily P.jointContinuity
  have hzA : (x, z) ∈ A.sourceLocus := by
    simpa [A] using hzRaw
  have hendpoint : A.GenericEndpointAgreement P.radius := by
    dsimp only [A]
    exact C.transportedLocalFamily_genericEndpointAgreement
      P.jointContinuity P.fixedTimeEndpoint
  have hendpointNorm : ‖A.normal (x, z)‖ < P.radius := by
    simpa [A] using htransportedEndpointNorm
  have hcontrol :
      z ∈ ((CartanSourceExponential.genericFamily g).normal x).source ∧
        ‖(CartanSourceExponential.genericFamily g).normal x z‖ <
          P.radius :=
    hendpoint.controlsGenericNormal x z hzA hendpointNorm
  have hnormalEq :
      A.normal (x, z) =
        (CartanSourceExponential.genericFamily g).normal x z :=
    hendpoint.normal_eq_generic hzA hendpointNorm
  have hzGenericNorm :
      ‖(CartanSourceExponential.genericFamily g).normal x z‖ <
        genericRadius := by
    rw [← hnormalEq]
    simpa [A] using htransportedGenericNorm
  have hxAnchor : x ∈ C.rawLocalFamily.anchors :=
    C.rawLocalFamily.sourceLocus_fst (x, z) hzRaw
  have hpTarget : p ∈ targets := hcontrolled.2
  rcases
      hadmissible x hxAnchor p hpTarget L z hcontrol.1 hzGenericNorm with
    ⟨package⟩
  exact ⟨package.comparison.genericData⟩

set_option maxHeartbeats 2000000 in
/-- A locally uniform transferred radius contains an honest open product
patch on which the same radius is admissible.  Naming the predicate as a set
keeps the dependent alignment quantifier out of product-neighborhood
elaboration. -/
theorem exists_open_source_target_patch_of_locallyUniformTransferredRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    {x₀ : M} {p₀ : RoundSphere3} {radius : ℝ}
    (hlocal : LocallyUniformTransferredNormalRadiusAt
      g (x₀, p₀) radius) :
    ∃ (U : Set M) (V : Set RoundSphere3),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ p₀ ∈ V ∧
        ∀ x ∈ U, ∀ p ∈ V,
          TransferredNormalRadiusAdmissible g x p radius := by
  let stableLocus : Set (M × RoundSphere3) :=
    {xp | TransferredNormalRadiusAdmissible g xp.1 xp.2 radius}
  have hlocal' : stableLocus ∈ 𝓝 (x₀, p₀) := by
    exact hlocal
  rcases mem_nhds_prod_iff.mp hlocal' with
    ⟨sourceSet, hsourceSet, targetSet, htargetSet, hproduct⟩
  rcases _root_.mem_nhds_iff.mp hsourceSet with
    ⟨U, hUsub, hopenU, hx₀U⟩
  rcases _root_.mem_nhds_iff.mp htargetSet with
    ⟨V, hVsub, hopenV, hp₀V⟩
  refine ⟨U, V, hopenU, hx₀U, hopenV, hp₀V, ?_⟩
  intro x hx p hp
  have hxp : (x, p) ∈ sourceSet ×ˢ targetSet :=
    ⟨hUsub hx, hVsub hp⟩
  have hmem : (x, p) ∈ stableLocus := hproduct hxp
  exact hmem

/-! ## Main persistence reduction -/

set_option maxHeartbeats 2000000 in
/--
Subordinate fixed-chart source agreement and locally persistent transferred
generic-normal radii imply the original raw fixed-chart generic-data
persistence contract.

The proof first chooses a product neighborhood on which one generic-normal
radius is admissible.  The source package is then subordinated to its source
factor.  Dividing the smaller of the ODE endpoint-agreement radius and the
admissible generic radius by the transition operator bound gives a raw normal
radius.  Endpoint agreement identifies the transported normal with the public
generic normal, and the retained transferred package supplies the requested
legacy generic datum.
-/
theorem fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_transferredRadiusStability
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hsource : SubordinateFixedChartMovingSourceAgreement g)
    (hstable : TransferredNormalRadiusLocalStability g) :
    FixedChartLocalGenericDataPersistence g := by
  intro x₀ p₀
  rcases hstable (x₀, p₀) with
    ⟨genericRadius, hgenericRadius, hlocal⟩
  rcases
      exists_open_source_target_patch_of_locallyUniformTransferredRadius
        hlocal with
    ⟨U, V, hopenU, hx₀U, hopenV, hp₀V, hpatch⟩
  have hUnhds : U ∈ 𝓝 x₀ := hopenU.mem_nhds hx₀U
  rcases hsource x₀ U hUnhds with
    ⟨C, P, hanchorsU, K, hK, hbound⟩
  have hbound' : ∀ x ∈ C.rawLocalFamily.anchors,
      ‖fixedToPreferredTransitionDerivative x₀ x‖ ≤ K := by
    intro x hx
    simpa [fixedToPreferredTransitionDerivative] using hbound x hx
  have hadmissible : ∀ x ∈ C.rawLocalFamily.anchors,
      ∀ p ∈ V, TransferredNormalRadiusAdmissible g x p genericRadius := by
    intro x hx p hp
    exact hpatch x (hanchorsU hx) p hp
  refine ⟨C, V, hopenV, hp₀V, min P.radius genericRadius / K,
    div_pos (lt_min P.radius_pos hgenericRadius) hK, ?_⟩
  exact controlledRawFixedChartLocus_subset_universalGenericData
    C P V hK hbound' hadmissible

/-! ## Open-locus discharge -/

section Curvature

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/--
Concrete open-locus form of the moving-anchor reduction.

The two open sets are independent of the fixed-chart raw inverse:

* `genericCanonicalChartAgreementLocus` concerns only the independently
  selected round-sphere target exponential and the canonical target family;
* `TransferredSuccessorPackageContinuationLocus` is conditional on the actual
  source-normal membership, canonical target-source membership, and target
  chart germ equality at the aligned vector.

Constant curvature is used only to put the complete diagonal inside the
conditional continuation locus.  All remaining source dependence is exposed
in `GenericSourceNormalLocalStability` and the fixed-chart transition
agreement above.
-/
theorem fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_openLoci
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfixedSource : SubordinateFixedChartMovingSourceAgreement g)
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htargetOpen : IsOpen genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    FixedChartLocalGenericDataPersistence g := by
  apply
    fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_transferredRadiusStability
      hfixedSource
  apply
    transferredNormalRadiusLocalStability_of_source_target_and_isOpen_packageLocus
      hcurv hgenericSource
  · intro p
    rw [htargetOpen.interior_eq]
    exact zero_mem_genericCanonicalChartAgreementLocus p
  · exact hpackageOpen

/-- Fully qualitative source form: the quantitative transition bound in the
preceding theorem is generated from operator-valued continuity at centers. -/
theorem fixedChartLocalGenericDataPersistence_of_transitionAgreement_of_continuousAtCenters_of_openLoci
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (htransition : SubordinateFixedChartTransitionAgreement g)
    (hcontinuous :
      FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M))
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htargetOpen : IsOpen genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    FixedChartLocalGenericDataPersistence g := by
  apply
    fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_openLoci
      hcurv
  · exact
      subordinateFixedChartMovingSourceAgreement_of_transitionAgreement_of_continuousAtCenters
        htransition hcontinuous
  · exact hgenericSource
  · exact htargetOpen
  · exact hpackageOpen

/-- The same concrete moving-parameter inputs directly provide the exact
local generic-data cover consumed by rooted recognition. -/
theorem localGenericSuccessorDataCover_of_subordinateMovingSource_of_openLoci
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfixedSource : SubordinateFixedChartMovingSourceAgreement g)
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htargetOpen : IsOpen genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    LocalGenericSuccessorDataCover g :=
  (fixedChartLocalGenericDataPersistence_of_subordinateMovingSource_of_openLoci
    hcurv hfixedSource hgenericSource htargetOpen hpackageOpen).toLocalGenericSuccessorDataCover

/-- Exact local-cover conclusion from the qualitative fixed-chart ODE
agreement, moving transition-derivative continuity, and the two explicit open
loci. -/
theorem localGenericSuccessorDataCover_of_transitionAgreement_of_continuousAtCenters_of_openLoci
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (htransition : SubordinateFixedChartTransitionAgreement g)
    (hcontinuous :
      FixedToPreferredTransitionDerivativeContinuousAtCenters (M := M))
    (hgenericSource : GenericSourceNormalLocalStability g)
    (htargetOpen : IsOpen genericCanonicalChartAgreementLocus)
    (hpackageOpen : IsOpen (TransferredSuccessorPackageContinuationLocus g)) :
    LocalGenericSuccessorDataCover g :=
  (fixedChartLocalGenericDataPersistence_of_transitionAgreement_of_continuousAtCenters_of_openLoci
    hcurv htransition hcontinuous hgenericSource htargetOpen hpackageOpen).toLocalGenericSuccessorDataCover

end Curvature

end CartanGenericSuccessorDataMovingPersistenceReduction
end Poincare
