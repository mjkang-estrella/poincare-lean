import Poincare.Global.DeTurckBUCSpatialVariationalTwoRestartPackage
import Poincare.Global.DeTurckBUCPointFlowVariationalSmoothDependence

/-!
# A nonautonomous variational hierarchy for the spatial two-restart package

For a nonautonomous ODE

`d/ds Phi s q = V s (Phi s q)`,

smoothness in the initial point is spatial.  It does not require joint
`ContDiff` regularity in `(s,q)`.  A coherent first-variation selector carries
an operator `J s q` with two independent properties:

* `J s q` is the Frechet derivative of the fixed-time endpoint in `q`;
* at a fixed initial point it solves
  `J' = fderiv (V s) (Phi s q) ∘ J`.

Those properties immediately identify the time derivative of the canonical
spatial differential, which is the mixed statement consumed by
`TwoRestartSpatialVariationalPointFlowPackage`.

Two further spatial endpoint-variation fields assemble fixed-time `C³`
through `LocalThirdOrderVariationalTower`.  No time derivative of `V`, no
joint time-space `ContDiff`, and no derivative-in-time conclusion for the
spatial differential is stored as a premise.  The fixed-time endpoint
identifications retained below are the standard outputs of the
parameterized-flow/Gronwall comparison.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function
open scoped ContDiff Topology

namespace Poincare

section AbstractNonautonomousHierarchy

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance nonautonomousFirstDerivativeNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance nonautonomousFirstDerivativeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

local instance nonautonomousSecondDerivativeNormedGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance nonautonomousSecondDerivativeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedSpace

local instance nonautonomousThirdDerivativeNormedGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance nonautonomousThirdDerivativeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))) :=
  ContinuousLinearMap.toNormedSpace

/-- A coherent nonautonomous first-variation selector germ.

`endpoint_hasFDerivAt_timeGerm` is the endpoint identification produced by
the ordinary parameterized-flow/Gronwall theorem.  `first_timeEquation` is
the first variational ODE supplied by the augmented selector.  Neither field
is the derivative-of-spatial-differential conclusion proved below. -/
structure CoherentNonautonomousFirstVariationSelectorGerm
    (V : ℝ → E → E) (Phi : ℝ → E → E)
    (t : ℝ) (z₀ : E) where
  first : ℝ → E → E →L[ℝ] E
  endpoint_hasFDerivAt_timeGerm :
    ∀ᶠ s in nhds t, HasFDerivAt (Phi s) (first s z₀) z₀
  first_timeEquation :
    HasDerivAt (fun s : ℝ ↦ first s z₀)
      ((fderiv ℝ (V t) (Phi t z₀)).comp (first t z₀)) t

namespace CoherentNonautonomousFirstVariationSelectorGerm

variable {V : ℝ → E → E} {Phi : ℝ → E → E}
variable {t : ℝ} {z₀ : E}

/-- The first-variation selector equation is exactly the time equation for
the canonical spatial differential of the endpoint family. -/
theorem forward_spatialDifferential_time
    (H : CoherentNonautonomousFirstVariationSelectorGerm V Phi t z₀) :
    HasDerivAt
      (fun s : ℝ ↦ fderiv ℝ (Phi s) z₀)
      ((fderiv ℝ (V t) (Phi t z₀)).comp
        (fderiv ℝ (Phi t) z₀)) t := by
  have heq :
      (fun s : ℝ ↦ fderiv ℝ (Phi s) z₀) =ᶠ[nhds t]
        (fun s : ℝ ↦ H.first s z₀) := by
    filter_upwards [H.endpoint_hasFDerivAt_timeGerm] with s hs
    exact hs.fderiv
  have htime := H.first_timeEquation.congr_of_eventuallyEq heq
  convert htime using 1
  exact congrArg
    (fun J : E →L[ℝ] E ↦ (fderiv ℝ (V t) (Phi t z₀)).comp J)
    heq.self_of_nhds

end CoherentNonautonomousFirstVariationSelectorGerm

/-- Fixed-time first-variation data for a restart endpoint.  This is the
spatial `C¹` half of a nonautonomous variational selector hierarchy. -/
structure CoherentFixedTimeFirstVariationSelectorHierarchy
    (f : E → E) (z₀ : E) where
  first : E → E →L[ℝ] E
  endpoint_hasFDerivAt_eventually :
    ∃ U ∈ nhds z₀, ∀ q ∈ U, HasFDerivAt f (first q) q
  first_contDiffAt_zero : ContDiffAt ℝ 0 first z₀

namespace CoherentFixedTimeFirstVariationSelectorHierarchy

variable {f : E → E} {z₀ : E}

/-- Convert the fixed-time selector hierarchy to the repository's generic
first-order variational data. -/
def toLocalFirstOrderVariationalData
    (H : CoherentFixedTimeFirstVariationSelectorHierarchy f z₀) :
    LocalFirstOrderVariationalData f z₀ where
  D₁ := H.first
  hasFDerivAt_eventually := H.endpoint_hasFDerivAt_eventually
  D₁_contDiffAt_zero := H.first_contDiffAt_zero

/-- A coherent fixed-time first variation proves spatial `C¹`. -/
theorem spatialC1
    (H : CoherentFixedTimeFirstVariationSelectorHierarchy f z₀) :
    ContDiffAt ℝ 1 f z₀ :=
  H.toLocalFirstOrderVariationalData.contDiffAt_one

end CoherentFixedTimeFirstVariationSelectorHierarchy

/-- Three coherent spatial endpoint variations for a nonautonomous flow.

The first field varies in time and carries the genuine first-variational ODE.
The second and third fields need only their fixed-time endpoint
identifications, exactly matching the anisotropic downstream contract. -/
structure CoherentNonautonomousThreeVariationSelectorHierarchy
    (V : ℝ → E → E) (Phi : ℝ → E → E)
    (t : ℝ) (z₀ : E)
    extends CoherentNonautonomousFirstVariationSelectorGerm V Phi t z₀ where
  second : ℝ → E → E →L[ℝ] (E →L[ℝ] E)
  third : ℝ → E → E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))
  endpoint_hasFDerivAt_eventually :
    ∃ U ∈ nhds z₀, ∀ q ∈ U,
      HasFDerivAt (Phi t) (first t q) q
  first_hasFDerivAt_eventually :
    ∃ U ∈ nhds z₀, ∀ q ∈ U,
      HasFDerivAt (first t) (second t q) q
  second_hasFDerivAt_eventually :
    ∃ U ∈ nhds z₀, ∀ q ∈ U,
      HasFDerivAt (second t) (third t q) q
  third_contDiffAt_zero : ContDiffAt ℝ 0 (third t) z₀

namespace CoherentNonautonomousThreeVariationSelectorHierarchy

variable {V : ℝ → E → E} {Phi : ℝ → E → E}
variable {t : ℝ} {z₀ : E}

/-- The three endpoint variations form the generic fixed-time derivative
tower. -/
def toLocalThirdOrderVariationalTower
    (H : CoherentNonautonomousThreeVariationSelectorHierarchy
      V Phi t z₀) :
    LocalThirdOrderVariationalTower (Phi t) z₀ where
  D₁ := H.first t
  D₂ := H.second t
  D₃ := H.third t
  f_hasFDerivAt_eventually := H.endpoint_hasFDerivAt_eventually
  D₁_hasFDerivAt_eventually := H.first_hasFDerivAt_eventually
  D₂_hasFDerivAt_eventually := H.second_hasFDerivAt_eventually
  D₃_contDiffAt_zero := H.third_contDiffAt_zero

/-- Three coherent spatial variations prove fixed-time spatial `C³`. -/
theorem forward_spatialC3
    (H : CoherentNonautonomousThreeVariationSelectorHierarchy
      V Phi t z₀) :
    ContDiffAt ℝ 3 (Phi t) z₀ :=
  H.toLocalThirdOrderVariationalTower.contDiffAt_three

/-- In particular, the same hierarchy proves fixed-time spatial `C¹`. -/
theorem forward_spatialC1
    (H : CoherentNonautonomousThreeVariationSelectorHierarchy
      V Phi t z₀) :
    ContDiffAt ℝ 1 (Phi t) z₀ :=
  H.forward_spatialC3.of_le (by norm_num)

/-- The time equation is inherited from the coherent first level, with no
joint time-space differentiability assumption. -/
theorem forward_spatialDifferential_time
    (H : CoherentNonautonomousThreeVariationSelectorHierarchy
      V Phi t z₀) :
    HasDerivAt
      (fun s : ℝ ↦ fderiv ℝ (Phi s) z₀)
      ((fderiv ℝ (V t) (Phi t z₀)).comp
        (fderiv ℝ (Phi t) z₀)) t :=
  CoherentNonautonomousFirstVariationSelectorGerm.forward_spatialDifferential_time
    H.toCoherentNonautonomousFirstVariationSelectorGerm

end CoherentNonautonomousThreeVariationSelectorHierarchy

/-- The asymmetric forward-three/backward-one hierarchy matching the exact
two-restart spatial package. -/
structure CoherentNonautonomousTwoRestartVariationalSelectorHierarchy
    (V : ℝ → E → E) (Phi Psi : ℝ → E → E)
    (t : ℝ) (z₀ y₁ : E) where
  forward : CoherentNonautonomousThreeVariationSelectorHierarchy
    V Phi t z₀
  backward : CoherentFixedTimeFirstVariationSelectorHierarchy
    (Psi 0) y₁

/-- A genuine nonautonomous forward-three/backward-one variational hierarchy
upgrades the ODE/restart core to the complete anisotropic package. -/
def TwoRestartPointFlowCore.toSpatialVariationalPointFlowPackage_of_coherentNonautonomousHierarchy
    {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
    {t : ℝ} {z₀ y₁ : E}
    (C : TwoRestartPointFlowCore V Phi Psi t z₀ y₁)
    (H : CoherentNonautonomousTwoRestartVariationalSelectorHierarchy
      V Phi Psi t z₀ y₁) :
    TwoRestartSpatialVariationalPointFlowPackage V Phi Psi t z₀ y₁ where
  core := C
  forward_spatialC3 := H.forward.forward_spatialC3
  backward_zero_spatialC1 := H.backward.spatialC1
  forward_spatialDifferential_time :=
    H.forward.forward_spatialDifferential_time

end AbstractNonautonomousHierarchy

end Poincare
