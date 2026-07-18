import Poincare.Global.DeTurckBUCInteriorTimeGermAssembly
import Poincare.Global.DeTurckBUCScalarEvolutionBridge

/-!
# Interior inverse-gauge intrinsic Ricci assembly

Time-germ assembly transfers the reconstructed inverse-gauge coordinate
equation to an independently assembled smooth metric family.  To identify
that coordinate equation with the intrinsic Ricci equation of the assembled
family, one further input is genuinely spatial: the trace of the reconstructed
coordinate curvature must be the preferred-chart expression of `-2 Ric` for
the assembled metric at the restart time.

This file keeps that curvature-rate equality explicit.  It is the spatial
half of the still-unconstructed joint spacetime pullback/metric germ; a
pointwise time germ alone cannot determine curvature.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

variable {ι κ : Type*}

/--
The reconstructed coordinate Ricci equation, an honest time germ into the
assembled family, and the explicit curvature-rate comparison identify both
intrinsic time differentiability and the pointwise equation
`timeDerivAt = -2 Ric`.
-/
theorem timeDerivAt_eq_neg_two_ricciAt_of_reconstructedInverseGaugeMetric_germ
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (hy : y ∈ (extChartAt I anchor).source)
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J) curv t)
    (hrate : ∀ p q : E,
      (-2 : ℝ) * LinearMap.trace ℝ E (curv p q) =
        CovariantDerivative.chartMetric
          (fun z : M ↦ (-2 : ℝ) • ricciContinuousBilinAt (rt t) z)
          anchor (extChartAt I anchor y) p q)
    (hmetric : ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        D K u₀ phi J s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (rt s).inner anchor (extChartAt I anchor y) p q)) :
    TimeDifferentiableAt rt t y ∧
      ∀ v w : TM y,
        timeDerivAt rt t y v w = -2 * (rt t).ricciAt y v w := by
  let H : ∀ z : M, TM z →L[ℝ] TM z →L[ℝ] ℝ :=
    fun z ↦ (-2 : ℝ) • ricciContinuousBilinAt (rt t) z
  have hlocal :=
    timeDerivAt_eq_tensorField_of_isCoordinateRicciFlowAt_chartMetric_germ
      rt (reconstructedInverseGaugeMetric D K u₀ phi J) curv H
      t anchor hy hflow (by simpa only [H] using hrate) hmetric
  refine ⟨hlocal.1, ?_⟩
  intro v w
  rw [hlocal.2 v w]
  simp [H, ricciContinuousBilinAt_apply]

/--
The assembled family therefore satisfies the intrinsic closed Ricci-flow
predicate at the represented spacetime point.
-/
theorem isClosedRicciFlowSolutionAt_of_reconstructedInverseGaugeMetric_germ
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (hy : y ∈ (extChartAt I anchor).source)
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J) curv t)
    (hrate : ∀ p q : E,
      (-2 : ℝ) * LinearMap.trace ℝ E (curv p q) =
        CovariantDerivative.chartMetric
          (fun z : M ↦ (-2 : ℝ) • ricciContinuousBilinAt (rt t) z)
          anchor (extChartAt I anchor y) p q)
    (hmetric : ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        D K u₀ phi J s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (rt s).inner anchor (extChartAt I anchor y) p q)) :
    IsClosedRicciFlowSolutionAt rt t y := by
  have hlocal :=
    timeDerivAt_eq_neg_two_ricciAt_of_reconstructedInverseGaugeMetric_germ
      D K u₀ phi J rt anchor hy curv hflow hrate hmetric
  exact isClosedRicciFlowSolutionAt_of_timeDerivAt_eq_neg_two_ricciAt
    rt t y hlocal.2

end Poincare
