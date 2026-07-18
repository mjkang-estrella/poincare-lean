import Poincare.Global.DeTurckBUCInteriorInverseGaugeEvolution

/-!
# Point-indexed interior inverse-gauge Ricci data

The self-chart interior theorem constructs a two-sided coordinate Ricci-flow
germ at one manifold point.  This file applies dependent choice to those
proved local outputs and exposes one coherent point-indexed family of
trajectories, variational differentials, and curvature rates.

No global smooth metric is assembled here.  The output is exactly the local
family later consumed by the time-germ and Hamilton assembly interfaces.
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

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Pointwise analytic and geometric reconstruction data select a family of
actual two-sided coordinate Ricci-flow germs, one in the self-chart of every
manifold point.  The selected curvature rate is the proved pullback of the
source Ricci curvature by the corresponding local inverse-gauge germ. -/
theorem exists_pointwise_reconstructedInverseGaugeRicciFlowData_of_metricEntries
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : M → ℝ≥0)
    (u₀ : ∀ y : M, SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) (K y))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (t : ℝ) (ht₀ : 0 < t)
    (htT : ∀ y : M, t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D y)).uniformLifespan (K y) : ℝ))
    (hfullGerm : ∀ y : M,
      (fun z' ↦ coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
              (D y)).uniformInteriorState (K y) (u₀ y) t +
            (D y).background) z') =ᶠ[nhds (extChartAt I y y)]
        CovariantDerivative.chartMetric (gt t).inner y)
    (hbackgroundGerm : ∀ y : M,
      (fun z' ↦ coordinateBilinearFormAt (D y).background z') =ᶠ[
          nhds (extChartAt I y y)]
        CovariantDerivative.chartMetric bg.inner y)
    (hremainder : ∀ y : M, ∀ v w : E,
      coordinateMetricValue
          ((D y).base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
                (D y)).uniformInteriorState (K y) (u₀ y) t +
              (D y).background)) (extChartAt I y y) v w =
        deTurckChartMetricEvolutionBilin gt bg y t
            (extChartAt I y y) v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
                (D y)).uniformInteriorState (K y) (u₀ y) t +
              (D y).background) (extChartAt I y y) v w +
          coordinateMetricLaplacianValue (D y).background
            (extChartAt I y y) v w)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t y 3) :
    ∃ phi : M → ℝ → E, ∃ J : M → ℝ → E →L[ℝ] E,
      ∃ curv : M → E → E → (E →ₗ[ℝ] E),
        (∀ y : M, phi y t = extChartAt I y y) ∧
          (∀ y : M, J y t = ContinuousLinearMap.id ℝ E) ∧
          ∀ y : M,
            IsCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric
                (D y) (K y) (u₀ y) (phi y) (J y))
              (curv y) t := by
  have hlocal (y : M) :=
    exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior_selfChart_of_metricEntries
      (D y) (K y) (u₀ y) gt bg y ht₀ (htT y)
      (hfullGerm y) (hbackgroundGerm y) (hremainder y) (hJoint y)
  choose phi J hphi hJ G hG hmetric hflow using hlocal
  let curv : M → E → E → (E →ₗ[ℝ] E) := fun y ↦
    pullbackCurvatureEnd (G y).tangentEquiv
      (chartRicciCurvatureEndAt (gt t) y
        (extChartAt I y y)
        ((extChartAt I y).map_source (mem_extChartAt_source y)))
  refine ⟨phi, J, curv, hphi, hJ, ?_⟩
  intro y
  simpa only [curv] using hflow y

end Poincare
