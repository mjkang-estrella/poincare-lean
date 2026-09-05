import Mathlib.Topology.CompactOpen
import Poincare.Global.MetricFlowJointCovRicciNormContinuity

/-!
# Covariant Ricci norm continuity for quotient-parameterized metric families

This module transfers the real-time continuity theorem for the squared norm of
the covariant Ricci derivative to a metric family whose parameter space is a
quotient of nonnegative real time.

The quotient-map hypothesis includes surjectivity. This is extra data and is
not supplied by the current reaction parameter records.
-/

noncomputable section

open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u} {K : Type v}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [TopologicalSpace K]

/-- A quotient realization of a metric family by nonnegative real time
transfers global joint continuity of the squared covariant Ricci norm to the
family parameter space. -/
theorem continuous_covRicciNormSqAt_metricFamily_of_quotient_realization
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {g : K → ClosedSmoothRiemannianMetric n M}
    {parameter : Set.Ici (0 : ℝ) → K}
    (hParameter : Topology.IsQuotientMap parameter)
    (hRealizes : ∀ t, g (parameter t) = gt t.1)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    Continuous (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) := by
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (ClosedSmoothModel n) M
  apply hParameter.continuous_lift_prod_left
  have hRealTime :
      Continuous (fun p : ℝ × M ↦ covRicciNormSqAt (gt p.1) p.2) :=
    continuous_covRicciNormSqAt_joint_of_metricEntriesJointContDiffAt_three hJoint
  let inclusion : Set.Ici (0 : ℝ) × M → ℝ × M :=
    fun p ↦ (p.1.1, p.2)
  have hInclusion : Continuous inclusion := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hRestricted := hRealTime.comp hInclusion
  change Continuous
    (fun p : Set.Ici (0 : ℝ) × M ↦
      covRicciNormSqAt (gt p.1.1) p.2) at hRestricted
  simpa only [hRealizes] using hRestricted

end Poincare
