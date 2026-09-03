import Poincare.Global.MetricFamilyThirdJetCovRicciContinuity

/-!
# Covariant-Ricci continuity from scalar metric-entry third jets

This module replaces operator-valued continuity assumptions on the blended
metric and its first three spatial jets with continuity of their scalar
coordinate components.  Finite dimensionality reconstructs the continuous
linear maps from those fixed-input components.  No differentiable structure
or parameter derivative on the parameter space is assumed.
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

/-- Scalar-component `C^{0,3}` spatial regularity of a cutoff-blended chart
metric at one parameter and manifold anchor.  Every assumption is continuity
of a real-valued fixed coordinate component. -/
structure MetricFamilyBlendedMetricEntryThirdJetContinuousAt
    {K : Type v} [TopologicalSpace K]
    (g : K → ClosedSmoothRiemannianMetric n M) (k₀ : K) (x : M) : Prop where
  value : ∀ i j : E, ContinuousAt
    (fun p : K × E ↦ anchorBlendedMetricFamily g x p.1 p.2 i j)
    (k₀, extChartAt I x x)
  firstSpatial : ∀ u i j : E, ContinuousAt
    (fun p : K × E ↦
      fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2 u i j)
    (k₀, extChartAt I x x)
  secondSpatial : ∀ u a i j : E, ContinuousAt
    (fun p : K × E ↦
      fderiv ℝ
        (fun z ↦ fderiv ℝ
          (anchorBlendedMetricFamily g x p.1) z u) p.2 a i j)
    (k₀, extChartAt I x x)
  thirdSpatial : ∀ u a b i j : E, ContinuousAt
    (fun p : K × E ↦
      fderiv ℝ
        (fun z ↦ fderiv ℝ
          (fun y ↦ fderiv ℝ
            (anchorBlendedMetricFamily g x p.1) y u) z a) p.2 b i j)
    (k₀, extChartAt I x x)

omit [T2Space M] in
/-- Finite-dimensional reconstruction turns scalar metric-entry third jets
into the operator-valued third-jet package. -/
theorem MetricFamilyBlendedMetricEntryThirdJetContinuousAt.toBlendedMetricThirdJetContinuousAt
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyBlendedMetricEntryThirdJetContinuousAt g k₀ x) :
    MetricFamilyBlendedMetricThirdJetContinuousAt g k₀ x where
  value := by
    have hPi : ContinuousAt
        (fun p : K × E ↦ fun i : E ↦ fun j : E ↦
          anchorBlendedMetricFamily g x p.1 p.2 i j)
        (k₀, extChartAt I x x) := by
      rw [continuousAt_pi]
      intro i
      rw [continuousAt_pi]
      exact h.value i
    apply continuousAt_clm_of_apply
    intro i
    apply continuousAt_clm_of_apply
    intro j
    exact continuousAt_pi.mp (continuousAt_pi.mp hPi i) j
  firstSpatial := by
    have hPi : ContinuousAt
        (fun p : K × E ↦ fun u : E ↦ fun i : E ↦ fun j : E ↦
          fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2 u i j)
        (k₀, extChartAt I x x) := by
      rw [continuousAt_pi]
      intro u
      rw [continuousAt_pi]
      intro i
      rw [continuousAt_pi]
      exact h.firstSpatial u i
    refine continuousAt_clm_of_apply
      (A := E) (B := E →L[ℝ] E →L[ℝ] ℝ) ?_
    intro u
    apply continuousAt_clm_of_apply
    intro i
    apply continuousAt_clm_of_apply
    intro j
    exact continuousAt_pi.mp
      (continuousAt_pi.mp (continuousAt_pi.mp hPi u) i) j
  secondSpatial u := by
    have hPi : ContinuousAt
        (fun p : K × E ↦ fun a : E ↦ fun i : E ↦ fun j : E ↦
          fderiv ℝ
            (fun z ↦ fderiv ℝ
              (anchorBlendedMetricFamily g x p.1) z u) p.2 a i j)
        (k₀, extChartAt I x x) := by
      rw [continuousAt_pi]
      intro a
      rw [continuousAt_pi]
      intro i
      rw [continuousAt_pi]
      exact h.secondSpatial u a i
    refine continuousAt_clm_of_apply
      (A := E) (B := E →L[ℝ] E →L[ℝ] ℝ) ?_
    intro a
    apply continuousAt_clm_of_apply
    intro i
    apply continuousAt_clm_of_apply
    intro j
    exact continuousAt_pi.mp
      (continuousAt_pi.mp (continuousAt_pi.mp hPi a) i) j
  thirdSpatial u a := by
    have hPi : ContinuousAt
        (fun p : K × E ↦ fun b : E ↦ fun i : E ↦ fun j : E ↦
          fderiv ℝ
            (fun z ↦ fderiv ℝ
              (fun y ↦ fderiv ℝ
                (anchorBlendedMetricFamily g x p.1) y u) z a) p.2 b i j)
        (k₀, extChartAt I x x) := by
      rw [continuousAt_pi]
      intro b
      rw [continuousAt_pi]
      intro i
      rw [continuousAt_pi]
      exact h.thirdSpatial u a b i
    refine continuousAt_clm_of_apply
      (A := E) (B := E →L[ℝ] E →L[ℝ] ℝ) ?_
    intro b
    apply continuousAt_clm_of_apply
    intro i
    apply continuousAt_clm_of_apply
    intro j
    exact continuousAt_pi.mp
      (continuousAt_pi.mp (continuousAt_pi.mp hPi b) i) j

/-- Scalar coordinate components of the blended metric through its third
spatial jet suffice for local joint continuity of the intrinsic squared
covariant-Ricci norm. -/
theorem continuousAt_covRicciNormSqAt_joint_of_metricFamilyEntryThirdJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyBlendedMetricEntryThirdJetContinuousAt g k₀ x) :
    ContinuousAt
      (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) (k₀, x) :=
  continuousAt_covRicciNormSqAt_joint_of_metricFamilyThirdJet
    h.toBlendedMetricThirdJetContinuousAt

/-- Scalar coordinate components of the blended metric through its third
spatial jet at every point suffice for global joint continuity of the
intrinsic squared covariant-Ricci norm. -/
theorem continuous_covRicciNormSqAt_joint_of_metricFamilyEntryThirdJets
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M}
    (h : ∀ k : K, ∀ x : M,
      MetricFamilyBlendedMetricEntryThirdJetContinuousAt g k x) :
    Continuous (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) := by
  exact continuous_covRicciNormSqAt_joint_of_metricFamilyThirdJets
    (fun k x ↦ (h k x).toBlendedMetricThirdJetContinuousAt)

end Poincare
