import Poincare.Global.CartanSourceExponentialFamily
import Poincare.Global.RegularVariationalSelectorJointC1
import Poincare.Global.LinearEndpointGronwall

/-!
# One-chart jointly regular source exponential selectors

The source-normal-coordinate boundary is not solved by choosing a separate
`GeodesicTransport.expAt` at every anchor.  In one fixed manifold chart the
geodesic vector field is fixed, while the charted anchor and initial velocity
are initial-state parameters of one regular Picard--Lindelof selector.  This
file packages the inverse-function-theorem part of that construction.

For an endpoint map `endpoint (z,v)`, joint strict differentiability together
with the two expected slice derivatives forces the derivative of
`(z,v) |-> (z, endpoint (z,v))` to be the invertible shear
`(a,b) |-> (a,a+b)`.  Consequently a *single* product partial homeomorphism
simultaneously supplies the local exponential maps at all nearby anchors and
their jointly continuous local inverses.

The final section constructs the regular variational selector for the fixed
charted geodesic field.  Identifying its two slice germs with the stationary
zero-velocity solution and the existing fixed-anchor exponential is kept as
an explicit theorem-level boundary below; no independently chosen family of
partial homeomorphisms is introduced.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanSourceExponentialLocalChartSelector

section AbstractInverse

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [CompleteSpace X]

/-- The linear anchor-endpoint shear `(a,b) |-> (a,a+b)`. -/
def anchorEndpointShear : (X × X) ≃L[ℝ] (X × X) where
  toFun q := (q.1, q.1 + q.2)
  invFun q := (q.1, q.2 - q.1)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  map_add' p q := by ext <;> simp [add_left_comm, add_comm]
  map_smul' c q := by ext <;> simp [smul_add]
  continuous_toFun := continuous_fst.prodMk (continuous_fst.add continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst)

@[simp]
theorem anchorEndpointShear_apply (q : X × X) :
    anchorEndpointShear q = (q.1, q.1 + q.2) :=
  rfl

@[simp]
theorem anchorEndpointShear_symm_apply (q : X × X) :
    anchorEndpointShear.symm q = (q.1, q.2 - q.1) :=
  rfl

/--
The two slice derivatives determine the full derivative of a jointly strictly
differentiable endpoint map.  This is the analytic block-triangular argument
needed for source-anchor stability.
-/
theorem hasStrictFDerivAt_anchorEndpoint_of_slice_derivatives
    (endpoint : X × X → X) (z₀ : X) (D : (X × X) →L[ℝ] X)
    (hjoint : HasStrictFDerivAt endpoint D (z₀, 0))
    (hanchor : HasFDerivAt (fun z : X => endpoint (z, 0))
      (ContinuousLinearMap.id ℝ X) z₀)
    (hvelocity : HasFDerivAt (fun v : X => endpoint (z₀, v))
      (ContinuousLinearMap.id ℝ X) 0) :
    HasStrictFDerivAt
      (fun q : X × X => (q.1, endpoint q))
      (anchorEndpointShear (X := X) : (X × X) →L[ℝ] (X × X))
      (z₀, 0) := by
  have hanchorComp : HasFDerivAt (fun z : X => endpoint (z, 0))
      (D.comp (ContinuousLinearMap.inl ℝ X X)) z₀ := by
    simpa using hjoint.hasFDerivAt.comp z₀ (hasFDerivAt_prodMk_left z₀ (0 : X))
  have hvelocityComp : HasFDerivAt (fun v : X => endpoint (z₀, v))
      (D.comp (ContinuousLinearMap.inr ℝ X X)) 0 := by
    simpa using hjoint.hasFDerivAt.comp (0 : X)
      (hasFDerivAt_prodMk_right z₀ (0 : X))
  have hDinl : D.comp (ContinuousLinearMap.inl ℝ X X) =
      ContinuousLinearMap.id ℝ X := hanchorComp.unique hanchor
  have hDinr : D.comp (ContinuousLinearMap.inr ℝ X X) =
      ContinuousLinearMap.id ℝ X := hvelocityComp.unique hvelocity
  have hD : D = ContinuousLinearMap.fst ℝ X X +
      ContinuousLinearMap.snd ℝ X X := by
    apply ContinuousLinearMap.ext
    intro q
    calc
      D q = D ((q.1, 0) + (0, q.2)) := by simp
      _ = D (q.1, 0) + D (0, q.2) := map_add D _ _
      _ = (D.comp (ContinuousLinearMap.inl ℝ X X)) q.1 +
          (D.comp (ContinuousLinearMap.inr ℝ X X)) q.2 := rfl
      _ = q.1 + q.2 := by rw [hDinl, hDinr]; rfl
      _ = (ContinuousLinearMap.fst ℝ X X +
          ContinuousLinearMap.snd ℝ X X) q := rfl
  have hprod := hasStrictFDerivAt_fst.prodMk hjoint
  convert hprod using 1
  apply ContinuousLinearMap.ext
  intro q
  simp [hD, anchorEndpointShear]

/--
The resulting one-chart anchor/velocity to anchor/endpoint local
homeomorphism.  Its inverse second projection is the jointly continuous normal
vector as a function of anchor and endpoint.
-/
def anchorEndpointOpenPartialHomeomorph
    (endpoint : X × X → X) (z₀ : X) (D : (X × X) →L[ℝ] X)
    (hjoint : HasStrictFDerivAt endpoint D (z₀, 0))
    (hanchor : HasFDerivAt (fun z : X => endpoint (z, 0))
      (ContinuousLinearMap.id ℝ X) z₀)
    (hvelocity : HasFDerivAt (fun v : X => endpoint (z₀, v))
      (ContinuousLinearMap.id ℝ X) 0) :
    OpenPartialHomeomorph (X × X) (X × X) :=
  (hasStrictFDerivAt_anchorEndpoint_of_slice_derivatives
    endpoint z₀ D hjoint hanchor hvelocity).toOpenPartialHomeomorph
      (fun q : X × X => (q.1, endpoint q))

@[simp]
theorem anchorEndpointOpenPartialHomeomorph_apply
    (endpoint : X × X → X) (z₀ : X) (D : (X × X) →L[ℝ] X)
    (hjoint : HasStrictFDerivAt endpoint D (z₀, 0))
    (hanchor : HasFDerivAt (fun z : X => endpoint (z, 0))
      (ContinuousLinearMap.id ℝ X) z₀)
    (hvelocity : HasFDerivAt (fun v : X => endpoint (z₀, v))
      (ContinuousLinearMap.id ℝ X) 0) (q : X × X) :
    anchorEndpointOpenPartialHomeomorph endpoint z₀ D hjoint hanchor hvelocity q =
      (q.1, endpoint q) :=
  congrFun
    (hasStrictFDerivAt_anchorEndpoint_of_slice_derivatives
      endpoint z₀ D hjoint hanchor hvelocity).toOpenPartialHomeomorph_coe q

theorem center_mem_anchorEndpointOpenPartialHomeomorph_source
    (endpoint : X × X → X) (z₀ : X) (D : (X × X) →L[ℝ] X)
    (hjoint : HasStrictFDerivAt endpoint D (z₀, 0))
    (hanchor : HasFDerivAt (fun z : X => endpoint (z, 0))
      (ContinuousLinearMap.id ℝ X) z₀)
    (hvelocity : HasFDerivAt (fun v : X => endpoint (z₀, v))
      (ContinuousLinearMap.id ℝ X) 0) :
    (z₀, 0) ∈
      (anchorEndpointOpenPartialHomeomorph endpoint z₀ D hjoint hanchor hvelocity).source :=
  (hasStrictFDerivAt_anchorEndpoint_of_slice_derivatives
    endpoint z₀ D hjoint hanchor hvelocity).mem_toOpenPartialHomeomorph_source

theorem center_image_mem_anchorEndpointOpenPartialHomeomorph_target
    (endpoint : X × X → X) (z₀ : X) (D : (X × X) →L[ℝ] X)
    (hjoint : HasStrictFDerivAt endpoint D (z₀, 0))
    (hanchor : HasFDerivAt (fun z : X => endpoint (z, 0))
      (ContinuousLinearMap.id ℝ X) z₀)
    (hvelocity : HasFDerivAt (fun v : X => endpoint (z₀, v))
      (ContinuousLinearMap.id ℝ X) 0) :
    (z₀, endpoint (z₀, 0)) ∈
      (anchorEndpointOpenPartialHomeomorph endpoint z₀ D hjoint hanchor hvelocity).target :=
  (hasStrictFDerivAt_anchorEndpoint_of_slice_derivatives
    endpoint z₀ D hjoint hanchor hvelocity).image_mem_toOpenPartialHomeomorph_target

end AbstractInverse

section GeodesicSelector

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The fixed-chart autonomous geodesic state field. -/
def fixedChartGeodesicField
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) : E × E → E × E :=
  geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)

/--
Unlike independently chosen fixed-anchor exponentials, one fixed chart admits
a single regular variational ODE selector whose initial state contains the
varying anchor coordinate and velocity.
-/
theorem exists_regularVariationalSelector_fixedChart_with_projected_protectedInnerBall_subset
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {U : Set (E × E)}
    (hU : U ∈ nhds (extChartAt I x₀ x₀, (0 : E))) :
    ∃ H : LocalRegularControlledContinuousAutonomousSelector
        (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
        ((extChartAt I x₀ x₀, (0 : E)),
          ContinuousLinearMap.id ℝ (E × E)),
      closedBall (extChartAt I x₀ x₀, (0 : E))
          H.projectFirstVariational.protectedInnerRadius ⊆ U := by
  let q₀ : E × E := (extChartAt I x₀ x₀, (0 : E))
  let J₀ : (E × E) →L[ℝ] (E × E) :=
    ContinuousLinearMap.id ℝ (E × E)
  have hUaug : Prod.fst ⁻¹' U ∈ nhds (q₀, J₀) :=
    continuous_fst.continuousAt.preimage_mem_nhds hU
  have hfield : ContDiffAt ℝ 1
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      (q₀, J₀) := by
    apply firstVariationalAugmentedField_contDiffAt_one_of_contDiffAt_two
    simpa [q₀, fixedChartGeodesicField] using
      (GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff_two
        (g := g) (x₀ := x₀)).contDiffAt
  rcases
      exists_localRegularControlledContinuousAutonomousSelector_of_contDiffAt_one_with_protectedInnerBall_subset
        (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
        (q₀, J₀) hfield hUaug with ⟨H, hH⟩
  refine ⟨H, ?_⟩
  intro q hq
  change (q, J₀) ∈ Prod.fst ⁻¹' U
  apply hH
  change (q, J₀) ∈ closedBall (q₀, J₀) H.protectedInnerRadius
  rw [Metric.mem_closedBall, Prod.dist_eq, dist_self,
    max_eq_left (dist_nonneg : 0 ≤ dist q q₀)]
  simpa [q₀, J₀,
    LocalRegularControlledContinuousAutonomousSelector.protectedInnerRadius,
    LocalRegularControlledContinuousAutonomousSelector.projectFirstVariational] using hq

/-- The unrestricted selector existence theorem is the universal-neighborhood case. -/
theorem exists_regularVariationalSelector_fixedChart
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    Nonempty
      (LocalRegularControlledContinuousAutonomousSelector
        (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
        ((extChartAt I x₀ x₀, (0 : E)),
          ContinuousLinearMap.id ℝ (E × E))) := by
  rcases
      exists_regularVariationalSelector_fixedChart_with_projected_protectedInnerBall_subset
        g x₀ (U := Set.univ) Filter.univ_mem with ⟨H, _hH⟩
  exact ⟨H⟩

/--
Endpoint coordinate of the fixed-chart selector at time `T`, with the initial
velocity normalized by `T⁻¹`.  This normalization is essential: its central
velocity derivative is the identity, whereas the unnormalized endpoint has
velocity derivative `T • id`.
-/
def normalizedSelectorEndpoint
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E)))
    (T : ℝ) (q : E × E) : E :=
  (H.projectFirstVariational.selector (q.1, T⁻¹ • q.2) T).1

/--
The normalized endpoint is jointly strictly differentiable in the varying
anchor coordinate and endpoint-scale velocity.  This is the affine adapter
from the regular selector's `(initial state, relative time)` API to the
Cartan source parameters `(anchor, normal vector)`.
-/
theorem normalizedSelectorEndpoint_exists_hasStrictFDerivAt
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E)))
    {T : ℝ}
    (hT : T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2)) :
    ∃ D : (E × E) →L[ℝ] E,
      HasStrictFDerivAt (normalizedSelectorEndpoint g x₀ H T) D
        (extChartAt I x₀ x₀, (0 : E)) := by
  let q₀ : E × E := (extChartAt I x₀ x₀, (0 : E))
  have hq₀ : q₀ ∈ ball q₀ (H.initialRadius : ℝ) :=
    mem_ball_self (by exact_mod_cast H.initialRadius_pos)
  have hselector := H.projectedUncurriedSelector_hasStrictFDerivAt hq₀ hT
  have hrescale : HasStrictFDerivAt
      (fun q : E × E => (q.1, T⁻¹ • q.2))
      ((ContinuousLinearMap.fst ℝ E E).prod
        (T⁻¹ • ContinuousLinearMap.snd ℝ E E)) q₀ := by
    simpa only [Pi.smul_apply] using
      hasStrictFDerivAt_fst.prodMk
        (hasStrictFDerivAt_snd.const_smul T⁻¹)
  have hembed : HasStrictFDerivAt
      (fun q : E × E => ((q.1, T⁻¹ • q.2), T))
      (((ContinuousLinearMap.fst ℝ E E).prod
          (T⁻¹ • ContinuousLinearMap.snd ℝ E E)).prod
        (0 : (E × E) →L[ℝ] ℝ)) q₀ := by
    exact hrescale.prodMk (hasStrictFDerivAt_const T q₀)
  have hselector' : HasStrictFDerivAt
      (Function.uncurry H.projectFirstVariational.selector)
      (H.projectedJointDerivative q₀ T)
      ((q₀.1, T⁻¹ • q₀.2), T) := by
    simpa [q₀] using hselector
  have hstate := hselector'.comp q₀ hembed
  have hendpoint := hasStrictFDerivAt_fst.comp q₀ hstate
  refine ⟨
    (ContinuousLinearMap.fst ℝ E E).comp
      ((H.projectedJointDerivative q₀ T).comp
        (((ContinuousLinearMap.fst ℝ E E).prod
          (T⁻¹ • ContinuousLinearMap.snd ℝ E E)).prod
            (0 : (E × E) →L[ℝ] ℝ))), ?_⟩
  simpa only [normalizedSelectorEndpoint, Function.uncurry, q₀] using hendpoint

end GeodesicSelector

end CartanSourceExponentialLocalChartSelector
end Poincare
