import Poincare.Global.AntilipschitzMathlib
import Poincare.Global.PinchedLimitPositiveEinstein

/-!
# Stationary limits of the normalized closed Ricci flow

The volume-normalized flow is expected to converge to a stationary metric.
This file identifies that endpoint without an additional geometric interface:
a stationary normalized right-hand side with positive mean scalar curvature is
exactly positive-Einstein existence, hence exactly the reduced Hamilton limit
payload.  The reverse direction uses the already-proved positivity of total
Riemannian volume, so the mean scalar is a genuine average rather than an
extra nonzero-volume hypothesis.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory
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

/-- Pointwise stationarity of the volume-normalized closed Ricci-flow
right-hand side. -/
def IsClosedNormalizedRicciStationary
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x : M) (u w : TM3 x), normalizedRicciFlowRHSAt g x u w = 0

/-- A stationary normalized metric is Einstein at every point, with the one
global factor `meanScalar g / 3`. -/
theorem isEinsteinAt_meanScalar_div_three_of_normalizedRicciStationary
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hstat : IsClosedNormalizedRicciStationary g) (x : M) :
    g.IsEinsteinAt (meanScalar g / 3) x := by
  rw [g.isEinsteinAt_iff]
  intro u w
  have h := hstat x u w
  unfold normalizedRicciFlowRHSAt at h
  norm_num at h ⊢
  linarith

/-- A stationary normalized metric with positive mean scalar curvature is a
positive Einstein metric. -/
theorem positiveEinsteinMetric3_of_normalizedRicciStationary
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hstat : IsClosedNormalizedRicciStationary g)
    (hmean : 0 < meanScalar g) :
    PositiveEinsteinMetric3 M := by
  refine ⟨g, meanScalar g / 3, div_pos hmean (by norm_num), ?_⟩
  exact isEinsteinAt_meanScalar_div_three_of_normalizedRicciStationary g hstat

/-- Positive Einstein existence supplies a stationary normalized metric with
positive mean scalar curvature.  Nonzero volume is discharged by the local
anti-Lipschitz chart theorem. -/
theorem exists_normalizedRicciStationary_of_positiveEinsteinMetric3
    (h : PositiveEinsteinMetric3 M) :
    ∃ g : ClosedSmoothRiemannianMetric 3 M,
      IsClosedNormalizedRicciStationary g ∧ 0 < meanScalar g := by
  rcases h with ⟨g, lam, hlam, hEin⟩
  have hvol : volumeMeasure g Set.univ ≠ 0 :=
    GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib g
  have hmean : meanScalar g = 3 * lam := by
    have h :=
      meanScalar_of_forall_isEinsteinAt_of_volume_ne_zero
        (g := g) hEin hvol
    norm_num at h ⊢
    exact h
  refine ⟨g, ?_, ?_⟩
  · intro x u w
    have hRic := (g.isEinsteinAt_iff lam x).1 (hEin x) u w
    unfold normalizedRicciFlowRHSAt
    rw [hRic, hmean]
    norm_num
    ring
  · rw [hmean]
    positivity

/-- The normalized stationary-limit payload is equivalent to positive
Einstein existence. -/
theorem exists_normalizedRicciStationary_iff_positiveEinsteinMetric3 :
    (∃ g : ClosedSmoothRiemannianMetric 3 M,
      IsClosedNormalizedRicciStationary g ∧ 0 < meanScalar g) ↔
      PositiveEinsteinMetric3 M := by
  constructor
  · rintro ⟨g, hstat, hmean⟩
    exact positiveEinsteinMetric3_of_normalizedRicciStationary g hstat hmean
  · exact exists_normalizedRicciStationary_of_positiveEinsteinMetric3

/-- Consequently, the normalized stationary-limit payload is also exactly the
reduced Hamilton pinched-limit payload. -/
theorem exists_normalizedRicciStationary_iff_hamiltonConvergencePinchedLimit3Core :
    (∃ g : ClosedSmoothRiemannianMetric 3 M,
      IsClosedNormalizedRicciStationary g ∧ 0 < meanScalar g) ↔
      HamiltonConvergencePinchedLimit3Core M := by
  rw [exists_normalizedRicciStationary_iff_positiveEinsteinMetric3,
    ← hamiltonConvergencePinchedLimit3Core_iff_positiveEinsteinMetric3]

end Poincare
