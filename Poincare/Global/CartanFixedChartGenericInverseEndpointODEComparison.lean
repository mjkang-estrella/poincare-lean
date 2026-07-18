import Poincare.Global.CartanFixedChartGenericInverseEndpointReduction
import Poincare.Global.ChartTransitionGeodesicMap

/-!
# Generic-inverse endpoint agreement from an ODE comparison

The remaining fixed-chart endpoint identity is not taken as an input here.
Instead, this file compares two independently specified target-chart curves:

* the fixed-chart regular selector, transported into the preferred chart at
  the moving anchor; and
* a preferred-chart geodesic curve whose final position evaluates the public
  charted exponential.

If both curves solve the same target-chart geodesic ODE, remain in one closed
ball, and have the transported common initial state, ODE uniqueness forces
their endpoint coordinates to agree.  A genuine overlap condition places the
fixed selector endpoint in the preferred chart source; the generic target
locus supplies the same fact for the generic inverse.  Preferred-chart
injectivity then gives `GenericInverseEndpointAgreement`.

The comparison package contains no equality between the two endpoints or
between the two curves.  It exposes the exact lower-level obligations needed
for a later construction from chart-transition covariance and the public
fixed-time exponential flow.
-/

noncomputable section

set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

open CartanSourceExponential
open CartanGenericSuccessorDataMovingPersistenceReduction

/-! ## The transported fixed-chart selector curve -/

/-- The projected fixed-chart selector started at the moving anchor, with
velocity normalized so that time `C.time` represents the tangent vector
`w`. -/
def normalizedSelectorTrajectory
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E) : ℝ → E × E :=
  C.selector.projectFirstVariational.selector
    (extChartAt I x₀ x, C.time⁻¹ • w)

/-- Read the fixed-chart selector trajectory in the preferred chart at its
moving anchor. -/
def preferredTransportedSelectorTrajectory
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E) : ℝ → E × E :=
  GeodesicTransport.chartTransitionState x₀ x
    (C.normalizedSelectorTrajectory x w)

/-- At the selected time, the first component of the transported trajectory
is definitionally the preferred-chart evaluation of `fixedTimeEndpoint`. -/
@[simp]
theorem preferredTransportedSelectorTrajectory_time_fst
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E) :
    (C.preferredTransportedSelectorTrajectory x w C.time).1 =
      extChartAt I x (C.fixedTimeEndpoint x w) :=
  rfl

/-- If the projected selector starts at its supplied state, transporting that
state gives the preferred anchor and the linearly transported normalized
velocity. -/
theorem preferredTransportedSelectorTrajectory_zero_of_selectorInitial
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    (hx : x ∈ C.rawLocalFamily.anchors)
    (hinitial : C.normalizedSelectorTrajectory x w 0 =
      (extChartAt I x₀ x, C.time⁻¹ • w)) :
    C.preferredTransportedSelectorTrajectory x w 0 =
      (extChartAt I x x,
        C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)) := by
  have hxSource : x ∈ (extChartAt I x₀).source := hx.1
  unfold preferredTransportedSelectorTrajectory
  simp only [GeodesicTransport.chartTransitionState]
  rw [hinitial]
  apply Prod.ext
  · change
      extChartAt I x ((extChartAt I x₀).symm (extChartAt I x₀ x)) =
        extChartAt I x x
    exact congrArg (extChartAt I x) ((extChartAt I x₀).left_inv hxSource)
  · simp [
      fixedToAnchorVelocity, map_smul]

/-! ## Lower-level ODE comparison package -/

/--
Two target-chart curves with the same normalized initial state and the same
geodesic ODE data on `[0,C.time]`.

`preferredTrajectory_endpoint` identifies only the independently supplied
preferred curve with the public exponential evaluation.  No field compares
that curve to the transported fixed-chart selector.  Their equality is a
theorem below, obtained from ODE uniqueness.
-/
structure GenericInverseEndpointODEComparison
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E) where
  preferredTrajectory : ℝ → E × E
  commonCenter : E × E
  commonRadius : ℝ
  selectorInitial : C.normalizedSelectorTrajectory x w 0 =
    (extChartAt I x₀ x, C.time⁻¹ • w)
  preferredInitial : preferredTrajectory 0 =
    (extChartAt I x x,
      C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w))
  transportedContinuous : ContinuousOn
    (C.preferredTransportedSelectorTrajectory x w)
    (Icc (0 : ℝ) C.time)
  preferredContinuous : ContinuousOn preferredTrajectory
    (Icc (0 : ℝ) C.time)
  transportedDerivative : ∀ t ∈ Ico (0 : ℝ) C.time,
    HasDerivWithinAt (C.preferredTransportedSelectorTrajectory x w)
      (geodesicFlowField
        (GeodesicTransport.chartChristoffelField g x)
        (C.preferredTransportedSelectorTrajectory x w t))
      (Ici t) t
  preferredDerivative : ∀ t ∈ Ico (0 : ℝ) C.time,
    HasDerivWithinAt preferredTrajectory
      (geodesicFlowField
        (GeodesicTransport.chartChristoffelField g x)
        (preferredTrajectory t))
      (Ici t) t
  transportedMem : ∀ t ∈ Ico (0 : ℝ) C.time,
    C.preferredTransportedSelectorTrajectory x w t ∈
      Metric.closedBall commonCenter commonRadius
  preferredMem : ∀ t ∈ Ico (0 : ℝ) C.time,
    preferredTrajectory t ∈ Metric.closedBall commonCenter commonRadius
  selectorPositionOverlap : ∀ t ∈ Icc (0 : ℝ) C.time,
    (extChartAt I x₀).symm
      (C.normalizedSelectorTrajectory x w t).1 ∈ (chartAt E x).source
  preferredTrajectory_endpoint :
    (preferredTrajectory C.time).1 =
      GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
        (fixedToAnchorVelocity x₀ (x, w))

namespace GenericInverseEndpointODEComparison

/-- The pathwise chart-overlap side condition includes the selected fixed
endpoint. -/
theorem fixedEndpoint_mem_preferredChartSource
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    (data : C.GenericInverseEndpointODEComparison x w) :
    C.fixedTimeEndpoint x w ∈ (chartAt E x).source := by
  have htime : C.time ∈ Icc (0 : ℝ) C.time :=
    ⟨C.time_pos.le, le_rfl⟩
  simpa [fixedTimeEndpoint, normalizedSelectorTrajectory,
    CartanSourceExponentialLocalChartSelector.normalizedSelectorEndpoint] using
      data.selectorPositionOverlap C.time htime

/-- ODE uniqueness identifies the transported selector and the independently
specified preferred trajectory on the complete comparison interval. -/
theorem eqOn_preferredTrajectory
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    (hx : x ∈ C.rawLocalFamily.anchors)
    (data : C.GenericInverseEndpointODEComparison x w) :
    EqOn (C.preferredTransportedSelectorTrajectory x w)
      data.preferredTrajectory (Icc (0 : ℝ) C.time) := by
  let F : E × E → E × E :=
    geodesicFlowField
      (GeodesicTransport.chartChristoffelField g x)
  rcases
      GeodesicTransport.geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
        g x data.commonCenter data.commonRadius with
    ⟨K, hK⟩
  have hinitial : C.preferredTransportedSelectorTrajectory x w 0 =
      data.preferredTrajectory 0 := by
    rw [C.preferredTransportedSelectorTrajectory_zero_of_selectorInitial
      hx data.selectorInitial, data.preferredInitial]
  refine ODE_solution_unique_of_mem_Icc_right
    (v := fun _ : ℝ => F)
    (s := fun _ : ℝ => Metric.closedBall data.commonCenter data.commonRadius)
    (K := K) ?_ data.transportedContinuous ?_ ?_
      data.preferredContinuous ?_ ?_ hinitial
  · intro _t _ht
    simpa [F] using hK
  · intro t ht
    simpa [F] using data.transportedDerivative t ht
  · intro t ht
    exact data.transportedMem t ht
  · intro t ht
    simpa [F] using data.preferredDerivative t ht
  · intro t ht
    exact data.preferredMem t ht

/-- In particular, the fixed selector endpoint and the public exponential
evaluation have the same preferred-chart coordinate. -/
theorem fixedEndpoint_preferredChart_eq_publicExp
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    (hx : x ∈ C.rawLocalFamily.anchors)
    (data : C.GenericInverseEndpointODEComparison x w) :
    (chartAt E x) (C.fixedTimeEndpoint x w) =
      GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
        (fixedToAnchorVelocity x₀ (x, w)) := by
  have htime : C.time ∈ Icc (0 : ℝ) C.time :=
    ⟨C.time_pos.le, le_rfl⟩
  have hstate := data.eqOn_preferredTrajectory hx htime
  calc
    (chartAt E x) (C.fixedTimeEndpoint x w) =
        (C.preferredTransportedSelectorTrajectory x w C.time).1 := by
      rw [C.preferredTransportedSelectorTrajectory_time_fst]
      rfl
    _ = (data.preferredTrajectory C.time).1 := congrArg Prod.fst hstate
    _ = GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
          (fixedToAnchorVelocity x₀ (x, w)) :=
      data.preferredTrajectory_endpoint

end GenericInverseEndpointODEComparison

/-! ## Discharge of the generic-inverse identity -/

/-- A comparison package for every relevant fixed-chart input.  This is an
ODE/evaluation contract, not an endpoint-equality contract. -/
def GenericInverseEndpointODEComparisonProvider
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
    (extChartAt I x₀ x, w) ∈ C.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      Nonempty (C.GenericInverseEndpointODEComparison x w)

/-- The lower-level ODE comparison provider proves the single
generic-inverse endpoint identity used by the transition-package reduction. -/
theorem genericInverseEndpointAgreement_of_odeComparison
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hcomparison : C.GenericInverseEndpointODEComparisonProvider) :
    C.GenericInverseEndpointAgreement := by
  intro x w hxAnchor hwSource htarget
  rcases hcomparison x w hxAnchor hwSource htarget with ⟨data⟩
  let z : M := (genericFamily g).symmEval
    (x, fixedToAnchorVelocity x₀ (x, w))
  have hfixedSource :
      C.fixedTimeEndpoint x w ∈ (chartAt E x).source :=
    data.fixedEndpoint_mem_preferredChartSource
  have hgenericSource : z ∈ (chartAt E x).source := by
    exact genericSymmEval_mem_preferredChartSource htarget
  have hcoordinate :
      (chartAt E x) (C.fixedTimeEndpoint x w) = (chartAt E x) z := by
    calc
      (chartAt E x) (C.fixedTimeEndpoint x w) =
          GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
            (fixedToAnchorVelocity x₀ (x, w)) :=
        data.fixedEndpoint_preferredChart_eq_publicExp hxAnchor
      _ = (chartAt E x) z := by
        exact
          (preferredChart_genericSymmEval_eq_expAtChart htarget).symm
  calc
    C.fixedTimeEndpoint x w =
        (chartAt E x).symm ((chartAt E x) (C.fixedTimeEndpoint x w)) :=
      ((chartAt E x).left_inv hfixedSource).symm
    _ = (chartAt E x).symm ((chartAt E x) z) :=
      congrArg (chartAt E x).symm hcoordinate
    _ = z := (chartAt E x).left_inv hgenericSource

/-- Consequently, moving-derivative continuity and the ODE comparison
provider produce an actual transition-agreement package after shrinking the
anchor slice. -/
theorem exists_restrictedTransitionAgreementPackage_of_odeComparison
    (C : FixedChartAnchorEndpointPackage g x₀)
    (htransition : ContinuousOn
      (fixedToPreferredTransitionDerivative x₀)
      C.rawLocalFamily.anchors)
    (hregular : GenericJointRegularity g)
    (hcomparison : C.GenericInverseEndpointODEComparisonProvider) :
    ∃ C' : FixedChartAnchorEndpointPackage g x₀,
      Nonempty C'.TransitionAgreementPackage :=
  C.exists_restrictedTransitionAgreementPackage_of_genericJointRegularity
    htransition hregular
      (C.genericInverseEndpointAgreement_of_odeComparison hcomparison)

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport

/-! ## Pointwise provider -/

namespace CartanFixedChartGenericInverseEndpointODEComparison

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanFixedChartGenericInverseEndpointReduction
open CartanGenericSuccessorDataMovingPersistenceReduction
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport

/-- At each center, one fixed-chart package with moving-derivative continuity
and a genuine target-chart ODE comparison provider. -/
def PointwiseFixedChartGenericInverseEndpointODEData
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ x₀ : M,
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      ContinuousOn (fixedToPreferredTransitionDerivative x₀)
        C.rawLocalFamily.anchors ∧
      C.GenericInverseEndpointODEComparisonProvider

/-- ODE comparison data imply the previously verified pointwise
generic-inverse endpoint data. -/
theorem pointwiseGenericInverseEndpointData_of_odeComparison
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hdata : PointwiseFixedChartGenericInverseEndpointODEData g) :
    PointwiseFixedChartGenericInverseEndpointData g := by
  intro x₀
  rcases hdata x₀ with ⟨C, htransition, hcomparison⟩
  exact ⟨C, htransition,
    C.genericInverseEndpointAgreement_of_odeComparison hcomparison⟩

end CartanFixedChartGenericInverseEndpointODEComparison
end Poincare
