import Poincare.Global.NormalizedFlowStationaryLimit

/-!
# Componentwise convergence closes the normalized-flow endpoint

This module isolates the final elementary limit argument after geometric
compactness has produced a smooth candidate limit.  Convergence of the metric,
Ricci tensor, and mean scalar makes the normalized right-hand side converge to
the right-hand side of the limit metric.  If the flow speed also converges to
zero, uniqueness of limits makes the limit stationary.  Positive limiting mean
scalar then gives the reduced Hamilton pinched-limit payload.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [SimplyConnectedSpace M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

/-- Concrete componentwise convergence data for a normalized flow candidate.
The last field is asymptotic stationarity of the same normalized right-hand
side, not a stationarity assertion about the limit metric. -/
structure NormalizedRicciFlowComponentConvergence
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (gLimit : ClosedSmoothRiemannianMetric 3 M) : Prop where
  metric : ∀ (x : M) (u w : TM3 x),
    Tendsto (fun t ↦ (gt t).inner x u w) atTop
      (nhds (gLimit.inner x u w))
  ricci : ∀ (x : M) (u w : TM3 x),
    Tendsto (fun t ↦ (gt t).ricciAt x u w) atTop
      (nhds (gLimit.ricciAt x u w))
  meanScalar : Tendsto (fun t ↦ meanScalar (gt t)) atTop
    (nhds (meanScalar gLimit))
  speed : ∀ (x : M) (u w : TM3 x),
    Tendsto (fun t ↦ normalizedRicciFlowRHSAt (gt t) x u w) atTop
      (nhds 0)

/-- Componentwise convergence of metric, Ricci tensor, and mean scalar makes
the normalized right-hand side converge to that of the candidate limit. -/
theorem tendsto_normalizedRicciFlowRHSAt_of_componentConvergence
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (h : NormalizedRicciFlowComponentConvergence gt gLimit)
    (x : M) (u w : TM3 x) :
    Tendsto (fun t ↦ normalizedRicciFlowRHSAt (gt t) x u w) atTop
      (nhds (normalizedRicciFlowRHSAt gLimit x u w)) := by
  have hRic :
      Tendsto (fun t ↦ (-2 : ℝ) * (gt t).ricciAt x u w) atTop
        (nhds ((-2 : ℝ) * gLimit.ricciAt x u w)) :=
    tendsto_const_nhds.mul (h.ricci x u w)
  have hMean :
      Tendsto (fun t ↦ (2 / (3 : ℝ)) * meanScalar (gt t)) atTop
        (nhds ((2 / (3 : ℝ)) * meanScalar gLimit)) :=
    tendsto_const_nhds.mul h.meanScalar
  have hMeanMetric :
      Tendsto
        (fun t ↦ (2 / (3 : ℝ)) * meanScalar (gt t) *
          (gt t).inner x u w) atTop
        (nhds ((2 / (3 : ℝ)) * meanScalar gLimit *
          gLimit.inner x u w)) :=
    hMean.mul (h.metric x u w)
  simpa [normalizedRicciFlowRHSAt] using hRic.add hMeanMetric

/-- The candidate metric in a componentwise convergent, asymptotically
stationary normalized flow is stationary. -/
theorem normalizedRicciStationary_of_componentConvergence
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (h : NormalizedRicciFlowComponentConvergence gt gLimit) :
    IsClosedNormalizedRicciStationary gLimit := by
  intro x u w
  exact tendsto_nhds_unique
    (tendsto_normalizedRicciFlowRHSAt_of_componentConvergence h x u w)
    (h.speed x u w)

/-- A componentwise convergent normalized flow with vanishing speed and
positive limiting mean scalar supplies the reduced Hamilton limit payload. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_componentConvergence
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (h : NormalizedRicciFlowComponentConvergence gt gLimit)
    (hmean : 0 < meanScalar gLimit) :
    HamiltonConvergencePinchedLimit3Core M := by
  rw [hamiltonConvergencePinchedLimit3Core_iff_positiveEinsteinMetric3]
  exact positiveEinsteinMetric3_of_normalizedRicciStationary gLimit
    (normalizedRicciStationary_of_componentConvergence h) hmean

end Poincare
