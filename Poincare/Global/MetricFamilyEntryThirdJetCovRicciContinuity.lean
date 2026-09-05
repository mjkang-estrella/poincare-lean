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

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

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

/-- Joint `C³` regularity of a real-time metric flow supplies continuity of
every scalar component of its cutoff-blended spatial metric jets through
order three. -/
theorem metricFamilyBlendedMetricEntryThirdJetContinuousAt_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    MetricFamilyBlendedMetricEntryThirdJetContinuousAt gt t₀ x := by
  let q : E := extChartAt I x x
  have hFamily : anchorBlendedMetricFamily gt x =
      anchorBlendedMetricFlow gt x := by
    rfl
  have hG : ContDiffAt ℝ 3
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    anchorBlendedMetricFlow_jointContDiffAt_three_of_metricEntries hJoint
  letI innerNormedAddCommGroup :
      NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI innerNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    inferInstance
  have hD₁ : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦
        fderiv ℝ (anchorBlendedMetricFlow gt x p.1) p.2) (t₀, q) :=
    contDiffAt_spatial_fderiv_of_joint_contDiffAt_three_vector
      (anchorBlendedMetricFlow gt x) t₀ q hG
  refine
    { value := ?_
      firstSpatial := ?_
      secondSpatial := ?_
      thirdSpatial := ?_ }
  · intro i j
    rw [hFamily]
    simpa [Function.uncurry, q] using
      ((hG.continuousAt.clm_apply continuousAt_const).clm_apply
        continuousAt_const)
  · intro u i j
    rw [hFamily]
    simpa [q] using
      (((hD₁.continuousAt.clm_apply continuousAt_const).clm_apply
        continuousAt_const).clm_apply continuousAt_const)
  · intro u a i j
    rw [hFamily]
    have hD₁u : ContDiffAt ℝ 2
        (Function.uncurry (fun t z ↦
          fderiv ℝ (anchorBlendedMetricFlow gt x t) z u)) (t₀, q) := by
      simpa [Function.uncurry] using hD₁.clm_apply contDiffAt_const
    have hD₂ := contDiffAt_spatial_fderiv_of_joint_contDiffAt_two_vector
      (fun t z ↦ fderiv ℝ (anchorBlendedMetricFlow gt x t) z u)
      t₀ q hD₁u
    simpa [q] using
      (((hD₂.continuousAt.clm_apply continuousAt_const).clm_apply
        continuousAt_const).clm_apply continuousAt_const)
  · intro u a b i j
    rw [hFamily]
    have hD₁u : ContDiffAt ℝ 2
        (Function.uncurry (fun t z ↦
          fderiv ℝ (anchorBlendedMetricFlow gt x t) z u)) (t₀, q) := by
      simpa [Function.uncurry] using hD₁.clm_apply contDiffAt_const
    have hD₂ : ContDiffAt ℝ 1
        (fun p : ℝ × E ↦
          fderiv ℝ
            (fun z ↦ fderiv ℝ
              (anchorBlendedMetricFlow gt x p.1) z u) p.2) (t₀, q) :=
      contDiffAt_spatial_fderiv_of_joint_contDiffAt_two_vector
        (fun t z ↦ fderiv ℝ (anchorBlendedMetricFlow gt x t) z u)
        t₀ q hD₁u
    have hD₂a : ContDiffAt ℝ 1
        (Function.uncurry (fun t z ↦
          fderiv ℝ
            (fun y ↦ fderiv ℝ
              (anchorBlendedMetricFlow gt x t) y u) z a)) (t₀, q) := by
      simpa [Function.uncurry] using hD₂.clm_apply contDiffAt_const
    have hD₃ := continuousAt_spatial_fderiv_of_joint_contDiffAt_one_vector
      (fun t z ↦
        fderiv ℝ
          (fun y ↦ fderiv ℝ
            (anchorBlendedMetricFlow gt x t) y u) z a)
      t₀ q hD₂a
    simpa [q] using
      (((hD₃.clm_apply continuousAt_const).clm_apply
        continuousAt_const).clm_apply continuousAt_const)

/-- Pointwise joint `C³` metric-entry regularity packages the scalar
cutoff-blended third jet at every real time and manifold point. -/
theorem metricFamilyBlendedMetricEntryThirdJets_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    ∀ t : ℝ, ∀ x : M,
      MetricFamilyBlendedMetricEntryThirdJetContinuousAt gt t x :=
  fun t x ↦
    metricFamilyBlendedMetricEntryThirdJetContinuousAt_of_metricEntriesJointContDiffAt_three
      (hJoint t x)

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
