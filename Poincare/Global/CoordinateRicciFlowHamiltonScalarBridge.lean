import Poincare.Global.DeTurckBUCScalarEvolutionJointMetricEntries

/-!
# Coordinate Ricci-flow germs to Hamilton scalar evolution

Chartwise two-sided Ricci-flow equations determine the intrinsic metric time
derivative once their coordinate metrics agree, as time germs, with one
assembled smooth metric family.  Joint `C³` metric-entry regularity then
supplies the remaining mixed time-space regularity in Hamilton's scalar
evolution formula.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Two-sided coordinate Ricci-flow germs in pointwise preferred charts give
Hamilton scalar evolution for an assembled metric family.  The curvature-rate
premise is exactly the chart expression of `-2 Ric`; the time-germ premise is
the honest local-to-global metric assembly boundary.  Joint `C³` entries
discharge all remaining scalar-evolution regularity.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_coordinateRicciFlow_charts_joint_entries
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (anchor : M → M)
    (g : M → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (curv : M → E → E → (E →ₗ[ℝ] E))
    (hsource : ∀ y : M, y ∈ (extChartAt I (anchor y)).source)
    (hflow : ∀ y : M, IsCoordinateRicciFlowAt (g y) (curv y) t₀)
    (hrate : ∀ y : M, ∀ p q : E,
      (-2 : ℝ) * LinearMap.trace ℝ E (curv y p q) =
        CovariantDerivative.chartMetric
          (fun z : M ↦ (-2 : ℝ) • ricciContinuousBilinAt (gt t₀) z)
          (anchor y) (extChartAt I (anchor y) y) p q)
    (hmetric : ∀ y : M, ∀ p q : E,
      (fun t : ℝ ↦ g y t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner (anchor y) (extChartAt I (anchor y) y) p q))
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  let H : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ :=
    fun y ↦ (-2 : ℝ) • ricciContinuousBilinAt (gt t₀) y
  have hlocal (y : M) :
      TimeDifferentiableAt gt t₀ y ∧
        ∀ v w : TM y, timeDerivAt gt t₀ y v w = H y v w :=
    timeDerivAt_eq_tensorField_of_isCoordinateRicciFlowAt_chartMetric_germ
      gt (g y) (curv y) H t₀ (anchor y) (hsource y)
        (hflow y) (hrate y) (hmetric y)
  have hRicciFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y := by
    intro y
    apply isClosedRicciFlowSolutionAt_of_timeDerivAt_eq_neg_two_ricciAt
    intro v w
    rw [(hlocal y).2 v w]
    simp [H, ricciContinuousBilinAt_apply]
  exact
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hRicciFlow hJoint

/--
Forward coordinate Ricci-flow equations on a closed time interval give
Hamilton scalar evolution at every strict interior time.  Interior membership
is exactly what upgrades each constrained coordinate derivative to the
ordinary two-sided derivative consumed by the assembled scalar-evolution
bridge.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_forwardCoordinateRicciFlow_charts_joint_entries_of_mem_Ioo
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (a b t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (anchor : M → M)
    (g : M → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (curv : M → E → E → (E →ₗ[ℝ] E))
    (hsource : ∀ y : M, y ∈ (extChartAt I (anchor y)).source)
    (hflow : ∀ y : M,
      IsForwardCoordinateRicciFlowAt (g y) (curv y) (Set.Icc a b) t₀)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hrate : ∀ y : M, ∀ p q : E,
      (-2 : ℝ) * LinearMap.trace ℝ E (curv y p q) =
        CovariantDerivative.chartMetric
          (fun z : M ↦ (-2 : ℝ) • ricciContinuousBilinAt (gt t₀) z)
          (anchor y) (extChartAt I (anchor y) y) p q)
    (hmetric : ∀ y : M, ∀ p q : E,
      (fun t : ℝ ↦ g y t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner (anchor y) (extChartAt I (anchor y) y) p q))
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  exact
    satisfiesHamiltonScalarEvolutionAt_of_coordinateRicciFlow_charts_joint_entries
      gt t₀ x anchor g curv hsource
      (fun y ↦ (hflow y).to_isCoordinateRicciFlowAt_of_mem_Ioo ht₀)
      hrate hmetric hJoint

end Poincare
