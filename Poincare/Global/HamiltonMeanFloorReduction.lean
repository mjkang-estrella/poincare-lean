import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.NormalizedFlowScalarLowerProfile
import Poincare.Global.MetricFlowJointScalarContinuity

/-!
# Initial scalar positivity and the normalization obstruction

Joint metric regularity supplies a continuous extension of the forward mean
scalar track, hence a normalization antiderivative. The scalar comparison
then supplies positive floors on compact time intervals. A bounded
antiderivative on the entire forward ray is incompatible with a positive
uniform mean floor; it cannot be used as a viable replacement core.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The normalized equation expresses the mean using scalar curvature and
metric speed at a single point, providing a continuous extension to real time. -/
theorem exists_continuous_meanScalar_extension_of_normalizedRicciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ∃ r : ℝ → ℝ, Continuous r ∧ ∀ t ∈ Ici (0 : ℝ), r t = meanScalar (gt t) := by
  classical
  let x : M := Classical.arbitrary M
  have hs : Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
    continuous_iff_continuousAt.mpr fun p ↦
      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three (hjoint p.1 p.2)
  let r : ℝ → ℝ := fun t ↦ (gt t).scalarAt x +
    traceMetricVariationAt (gt t) (timeDerivAt gt t) x / 2
  refine ⟨r, ?_, ?_⟩
  · exact (hs.comp (continuous_id.prodMk continuous_const)).add
      (((HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv gt hjoint).comp
        (continuous_id.prodMk continuous_const)).div_const 2)
  · intro t ht
    dsimp [r]
    rw [traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      (hflow t ht x) (by norm_num)]
    ring

/-- Mean scalar continuity on the forward ray requires no moving-integral
hypothesis for a jointly regular normalized flow. -/
theorem continuousOn_meanScalar_of_normalizedRicciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ContinuousOn (fun t ↦ meanScalar (gt t)) (Ici (0 : ℝ)) := by
  obtain ⟨r, hr, heq⟩ :=
    exists_continuous_meanScalar_extension_of_normalizedRicciFlow gt hflow hjoint
  exact hr.continuousOn.congr (fun t ht ↦ (heq t ht).symm)

/-- Integrating a continuous extension constructs an ordinary derivative even
at time zero. Its increments on the forward ray integrate `(2/3) meanScalar`. -/
theorem exists_normalizationPrimitive_of_normalizedRicciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ∃ P : ℝ → ℝ, Continuous P ∧ P 0 = 0 ∧
      ∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t := by
  obtain ⟨r, hr, heq⟩ :=
    exists_continuous_meanScalar_extension_of_normalizedRicciFlow gt hflow hjoint
  let f : ℝ → ℝ := fun t ↦ (2 / 3 : ℝ) * r t
  have hf : Continuous f := continuous_const.mul hr
  refine ⟨fun t ↦ ∫ s in (0 : ℝ)..t, f s,
    (intervalIntegral.differentiable_integral_of_continuous (a := 0) hf).continuous,
    by simp, ?_⟩
  intro t ht
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  simpa only [f, heq t ht] using hd

/-- Positive initial scalar curvature gives an explicit positive mean profile.
The profile is allowed to decrease with time. -/
theorem meanScalar_lower_profile_of_initial_scalar_pos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hinit : ∀ x, 0 < (gt 0).scalarAt x) :
    ∃ (rho : ℝ) (P : ℝ → ℝ), 0 < rho ∧ Continuous P ∧ P 0 = 0 ∧
      (∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t) ∧
      ∀ t ∈ Ici (0 : ℝ),
        (rho / 2) * Real.exp (-P t) ≤ meanScalar (gt t) := by
  obtain ⟨P, hP, hP0, hd⟩ := exists_normalizationPrimitive_of_normalizedRicciFlow gt hflow hjoint
  obtain ⟨rho, hrho, hlow⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
  have hs : Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
    continuous_iff_continuousAt.mpr fun p ↦
      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three (hjoint p.1 p.2)
  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
  have hp := normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
    (gt := gt) (t0 := 0) hrho (by simpa only [zero_add] using hs)
    (fun t ht x ↦ by
      simpa only [zero_add] using
        satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
          (x := x) (hflow t ht) hL)
    (fun t ht x ↦ by
      simpa only [zero_add] using scalarAt_contMDiffAt_two_of_normalizedRicciFlow
        (hflow t ht) (hL.timeVariationEntries t) x)
    P hP (by simpa only [zero_add] using hd) hlow
  refine ⟨rho, P, hrho, hP, hP0, hd, ?_⟩
  intro t ht
  apply le_meanScalar_of_forall_le_scalarAt
  intro x
  simpa only [zero_add, hP0, sub_zero] using (hp t ht x).le

/-- A positive floor follows on each fixed compact forward time interval.
The witness may depend on the endpoint. -/
theorem meanScalar_floor_on_Icc_of_initial_scalar_pos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hinit : ∀ x, 0 < (gt 0).scalarAt x) (T : ℝ) (hT : 0 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc (0 : ℝ) T, c ≤ meanScalar (gt t) := by
  obtain ⟨rho, P, hrho, hP, _, _, hlow⟩ :=
    meanScalar_lower_profile_of_initial_scalar_pos gt hflow hjoint hinit
  obtain ⟨tmax, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    hP.continuousOn
  refine ⟨(rho / 2) * Real.exp (-P tmax),
    mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _), ?_⟩
  intro t ht
  exact (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (hmax ht)))
    (div_nonneg hrho.le (by norm_num))).trans (hlow t ht.1)

/-- A positive uniform mean floor forces every normalization antiderivative
to exceed every proposed upper bound on its forward increments. -/
theorem normalizationPrimitive_unbounded_of_meanScalar_floor
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (P : ℝ → ℝ)
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t)
    {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) :
    ∀ C : ℝ, ∃ t ∈ Ici (0 : ℝ), C < P t - P 0 := by
  have hg (t : ℝ) (ht : 0 ≤ t) : (2 / 3 : ℝ) * c * t ≤ P t - P 0 := by
    have h := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
      (C := (2 / 3 : ℝ) * c)
      (fun s hs ↦ by
        rw [(hd s (interior_subset hs)).deriv]
        exact mul_le_mul_of_nonneg_left (hfloor ⟨s, interior_subset hs⟩) (by norm_num))
      0 (by simp) t ht ht
    simpa only [sub_zero] using h
  intro C
  let t : ℝ := (|C| + 1) / ((2 / 3 : ℝ) * c)
  have hden : 0 < (2 / 3 : ℝ) * c := mul_pos (by norm_num) hc
  have ht : 0 ≤ t := (div_pos (by positivity) hden).le
  refine ⟨t, ht, ?_⟩
  have heq : (2 / 3 : ℝ) * c * t = |C| + 1 := mul_div_cancel₀ _ hden.ne'
  have hbound := hg t ht
  rw [heq] at hbound
  linarith [le_abs_self C]

end Poincare
