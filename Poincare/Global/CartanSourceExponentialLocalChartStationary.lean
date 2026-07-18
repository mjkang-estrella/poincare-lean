import Poincare.Global.CartanSourceExponentialLocalChartSelector

/-!
# Stationary slices of a retained source geodesic selector

A controlled Picard--Lindelof selector cannot make an arbitrary choice at an
equilibrium of its autonomous field.  The constant curve and the selected
curve solve the same Lipschitz ODE on the retained closed interval, so interval
uniqueness identifies them everywhere.

For the fixed-chart geodesic field every state `(z, 0)` is an equilibrium.
Consequently the jointly regular selector constructed for the source
exponential family fixes every nearby anchor on its entire retained time
interval.  This discharges the stationary-anchor slice required by the
anchor/endpoint inverse-function construction; only the rescaled velocity
slice remains to be identified.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

section StationarySelector

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {F : X → X} {x₀ q : X}

namespace LocalControlledContinuousAutonomousSelector

/-- A retained controlled selector is the constant curve at every equilibrium
initial state in its initial ball. -/
theorem selector_eq_initial_of_field_eq_zero
    (H : LocalControlledContinuousAutonomousSelector F x₀)
    (hq : q ∈ closedBall x₀ (H.initialRadius : ℝ))
    (hFq : F q = 0) :
    ∀ t ∈ Icc (-H.epsilon) H.epsilon, H.selector q t = q := by
  have hdata := H.selector_data q hq
  have hzero : (0 : ℝ) ∈ Ioo (-H.epsilon) H.epsilon := by
    constructor <;> linarith [H.epsilon_pos]
  have hqTube : q ∈ closedBall x₀ (H.tubeRadius : ℝ) := by
    simpa [hdata.1] using hdata.2.2 0 (Ioo_subset_Icc_self hzero)
  have heq : EqOn (H.selector q) (fun _ : ℝ => q)
      (Icc (-H.epsilon) H.epsilon) := by
    refine ODE_solution_unique_of_mem_Icc
      (v := fun _ : ℝ => F)
      (s := fun _ : ℝ => closedBall x₀ (H.tubeRadius : ℝ))
      (K := H.lipschitzConstant) (t₀ := 0) ?_ hzero ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro _t _ht
      exact H.field_lipschitzOn
    · exact HasDerivWithinAt.continuousOn hdata.2.1
    · intro t ht
      exact (hdata.2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · intro t ht
      exact hdata.2.2 t (Ioo_subset_Icc_self ht)
    · exact continuous_const.continuousOn
    · intro t _ht
      simpa [hFq] using (hasDerivAt_const t q)
    · intro _t _ht
      exact hqTube
    · simpa using hdata.1
  intro t ht
  exact heq ht

end LocalControlledContinuousAutonomousSelector

end StationarySelector

namespace CartanSourceExponentialLocalChartSelector

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

@[simp]
theorem fixedChartGeodesicField_zeroVelocity
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (z : E) :
    fixedChartGeodesicField g x₀ (z, (0 : E)) = 0 := by
  simp [fixedChartGeodesicField, geodesicFlowField]

/-- The projected fixed-chart geodesic selector fixes every nearby
zero-velocity state throughout the complete retained interval. -/
theorem projectedSelector_zeroVelocity_eq_initial
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E)))
    {z : E}
    (hz : (z, (0 : E)) ∈
      Metric.closedBall (extChartAt I x₀ x₀, (0 : E))
        (H.initialRadius : ℝ)) :
    ∀ t ∈ Icc (-H.epsilon) H.epsilon,
      H.projectFirstVariational.selector (z, (0 : E)) t = (z, (0 : E)) := by
  exact H.projectFirstVariational.selector_eq_initial_of_field_eq_zero
    hz (fixedChartGeodesicField_zeroVelocity g x₀ z)

/-- Position-component form of the stationary anchor slice consumed by the
joint anchor/endpoint inverse-function theorem. -/
theorem projectedSelector_zeroVelocity_fst_eq_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E)))
    {z : E}
    (hz : (z, (0 : E)) ∈
      Metric.closedBall (extChartAt I x₀ x₀, (0 : E))
        (H.initialRadius : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-H.epsilon) H.epsilon) :
    (H.projectFirstVariational.selector (z, (0 : E)) t).1 = z := by
  rw [projectedSelector_zeroVelocity_eq_initial g x₀ H hz t ht]

end CartanSourceExponentialLocalChartSelector

end Poincare
