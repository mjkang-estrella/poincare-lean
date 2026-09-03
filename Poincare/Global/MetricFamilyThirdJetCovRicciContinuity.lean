import Poincare.Global.MetricFamilyCovRicciEntryContinuity

/-!
# Covariant-Ricci continuity from spatial third jets of a metric family

This module packages the concrete `C^{0,3}` input needed to obtain joint
continuity of the squared covariant-Ricci norm for a metric family over an
arbitrary topological parameter space.  Here `C^{0,3}` means continuity in
the parameter and chart variables of the metric and its spatial derivatives
through order three.  No derivative in the parameter space is assumed.
-/

noncomputable section

open Bundle Filter Function
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- `C^{0,3}` spatial regularity of the cutoff-blended chart metric at one
parameter and manifold anchor.  The four fields assert joint continuity in
`K × E` of the value and the first three spatial jets; they impose no
differentiable structure or derivatives on `K`. -/
structure MetricFamilyBlendedMetricThirdJetContinuousAt
    {K : Type v} [TopologicalSpace K]
    (g : K → ClosedSmoothRiemannianMetric n M) (k₀ : K) (x : M) : Prop where
  value : ContinuousAt
    (Function.uncurry (anchorBlendedMetricFamily g x))
    (k₀, extChartAt I x x)
  firstSpatial : ContinuousAt
    (fun p : K × E ↦
      fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
    (k₀, extChartAt I x x)
  secondSpatial : ∀ u : E, ContinuousAt
    (fun p : K × E ↦
      fderiv ℝ
        (fun z ↦ fderiv ℝ
          (anchorBlendedMetricFamily g x p.1) z u) p.2)
    (k₀, extChartAt I x x)
  thirdSpatial : ∀ u a : E, ContinuousAt
    (fun p : K × E ↦
      fderiv ℝ
        (fun z ↦ fderiv ℝ
          (fun y ↦ fderiv ℝ
            (anchorBlendedMetricFamily g x p.1) y u) z a) p.2)
    (k₀, extChartAt I x x)

omit [T2Space M] in
/-- The packaged spatial third jet constructs the full Ricci chart jet. -/
theorem MetricFamilyBlendedMetricThirdJetContinuousAt.toRicciJetChartContinuousAt
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyBlendedMetricThirdJetContinuousAt g k₀ x) :
    MetricFamilyRicciJetChartContinuousAt g k₀ x :=
  metricFamilyRicciJetChartContinuousAt_of_metricThirdJets
    h.value h.firstSpatial h.secondSpatial h.thirdSpatial

omit [T2Space M] in
/-- The packaged spatial third jet supplies the inverse coefficients and
coordinate covariant-Ricci entries used by the chart contraction. -/
theorem MetricFamilyBlendedMetricThirdJetContinuousAt.toCovRicciChartContinuousAt
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyBlendedMetricThirdJetContinuousAt g k₀ x) :
    MetricFamilyCovRicciChartContinuousAt g k₀ x :=
  metricFamilyCovRicciChartContinuousAt_of_ricciJet
    h.toRicciJetChartContinuousAt

/-- A `C^{0,3}` spatial metric-family jet at one anchor gives joint
continuity of the intrinsic squared covariant-Ricci norm there. -/
theorem continuousAt_covRicciNormSqAt_joint_of_metricFamilyThirdJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyBlendedMetricThirdJetContinuousAt g k₀ x) :
    ContinuousAt
      (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) (k₀, x) :=
  continuousAt_covRicciNormSqAt_joint_of_chartContinuous
    h.toCovRicciChartContinuousAt

/-- `C^{0,3}` spatial regularity at every parameter-manifold point gives the
global joint continuity consumed by the analytic-data constructors.  The
parameter space remains merely topological. -/
theorem continuous_covRicciNormSqAt_joint_of_metricFamilyThirdJets
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M}
    (h : ∀ k : K, ∀ x : M,
      MetricFamilyBlendedMetricThirdJetContinuousAt g k x) :
    Continuous (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨k, x⟩
  exact continuousAt_covRicciNormSqAt_joint_of_metricFamilyThirdJet (h k x)

end Poincare
