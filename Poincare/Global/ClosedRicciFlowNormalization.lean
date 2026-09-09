import Poincare.Global.NormalizedFlowRescaling
import Poincare.Global.MetricRescaleFiniteAtlasIntegrals
import Poincare.Global.MetricRescaleFiniteAtlasForwardFlow
import Poincare.Global.HamiltonChartDensityLocalDomination
import Poincare.Global.MetricFlowJointScalarContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

set_option autoImplicit false

universe u

namespace Poincare.ClosedRicciFlowNormalization

section Manifold

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [SecondCountableTopology M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

def normalizedFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x

def regularRicciFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x) ∧
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, MetricEntriesJointContDiffAt gt t x 3

def normalizationGoal : Prop :=
  (∀ g₀ : ClosedSmoothRiemannianMetric 3 M, regularRicciFlowGoal g₀) →
  ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, normalizedFlowGoal g₀

end Manifold

/-- The scale in base time, for a supplied real mean-curvature track. -/
def baseScale (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp ((2 / 3 : ℝ) * ∫ s in (0 : ℝ)..t, r s)

/-- Normalized time as a function of base time. -/
def normalizedTime (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, baseScale r s

theorem baseScale_pos (r : ℝ → ℝ) (t : ℝ) : 0 < baseScale r t :=
  Real.exp_pos _

theorem baseScale_zero (r : ℝ → ℝ) : baseScale r 0 = 1 := by
  simp [baseScale]

theorem normalizedTime_zero (r : ℝ → ℝ) : normalizedTime r 0 = 0 := by
  simp [normalizedTime]

theorem hasDerivAt_baseScale {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    HasDerivAt (baseScale r) ((2 / 3 : ℝ) * r t * baseScale r t) t := by
  have h := ((hr.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul
    (2 / 3 : ℝ)).exp
  simpa only [baseScale, mul_comm] using h

theorem continuous_baseScale {r : ℝ → ℝ} (hr : Continuous r) :
    Continuous (baseScale r) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_baseScale hr t).continuousAt

theorem hasStrictDerivAt_normalizedTime {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    HasStrictDerivAt (normalizedTime r) (baseScale r t) t :=
  (continuous_baseScale hr).integral_hasStrictDerivAt 0 t

theorem strictMono_normalizedTime {r : ℝ → ℝ} (hr : Continuous r) :
    StrictMono (normalizedTime r) :=
  strictMono_of_hasDerivAt_pos
    (fun t ↦ (hasStrictDerivAt_normalizedTime hr t).hasDerivAt) (baseScale_pos r)

/-- A continuous scalar track supplies both differential equations, including
ordinary derivatives at zero, on a positive interval of reached base times. -/
theorem exists_normalizingTimeData {r : ℝ → ℝ} (hr : Continuous r)
    {T : ℝ} (hT : 0 < T) :
    ∃ (S : ℝ) (τ c : ℝ → ℝ),
      0 < S ∧ τ 0 = 0 ∧ c 0 = 1 ∧ (∀ t, 0 < c t) ∧
      MapsTo τ (Ico 0 S) (Ico 0 T) ∧
      ∀ t ∈ Ico 0 S,
        normalizedTime r (τ t) = t ∧ c t = baseScale r (τ t) ∧
        HasDerivAt τ (c t)⁻¹ t ∧
        HasDerivAt c ((2 / 3 : ℝ) * r (τ t)) t := by
  let hf := (hasStrictDerivAt_normalizedTime hr 0).hasStrictFDerivAt_equiv
    (baseScale_pos r 0).ne'
  let e : OpenPartialHomeomorph ℝ ℝ := hf.toOpenPartialHomeomorph (normalizedTime r)
  have hsource : (0 : ℝ) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source
  have he0 : e 0 = 0 := normalizedTime_zero r
  have htarget : (0 : ℝ) ∈ e.target := he0 ▸ e.map_source hsource
  have hinv0 : e.symm 0 = 0 := by
    simpa only [he0] using e.left_inv hsource
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ e.target ∧ e.symm t < T := by
    have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), e.symm t < T :=
      (e.symm.continuousAt htarget).eventually
        (Iio_mem_nhds (by simpa [hinv0] using hT))
    filter_upwards [e.open_target.mem_nhds htarget, hlt] with t ht hlt'
    exact ⟨ht, hlt'⟩
  obtain ⟨a, S, haS, hsub⟩ := hnear.exists_Ioo_subset
  refine ⟨S, e.symm, (fun t ↦ baseScale r (e.symm t)), haS.2, hinv0,
    ?_, (fun t ↦ baseScale_pos r _), ?_, ?_⟩
  · simp [hinv0, baseScale_zero]
  · intro t ht
    have hp := hsub (show t ∈ Ioo a S from ⟨lt_of_lt_of_le haS.1 ht.1, ht.2⟩)
    refine ⟨?_, hp.2⟩
    apply (strictMono_normalizedTime hr).le_iff_le.mp
    change e 0 ≤ e (e.symm t)
    rw [he0, e.right_inv hp.1]
    exact ht.1
  · intro t ht
    have hp := hsub (show t ∈ Ioo a S from ⟨lt_of_lt_of_le haS.1 ht.1, ht.2⟩)
    have hd : HasDerivAt e.symm (baseScale r (e.symm t))⁻¹ t :=
      e.hasDerivAt_symm hp.1 (baseScale_pos r _).ne'
        (hasStrictDerivAt_normalizedTime hr _).hasDerivAt
    refine ⟨e.right_inv hp.1, rfl, hd, ?_⟩
    convert (hasDerivAt_baseScale hr (e.symm t)).comp t hd using 1
    field_simp [(baseScale_pos r (e.symm t)).ne']

section Manifold

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- The finite-interval construction requires only continuity of the actual
mean scalar on the retained base interval. All measure and time data used
by the rescaling adapter are produced here. -/
theorem normalizedFlowGoal_of_continuousOn_meanScalar
    (g₀ : ClosedSmoothRiemannianMetric 3 M)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {T : ℝ} (hT : 0 < T) (h0 : gt 0 = g₀)
    (hflow : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hmean : ContinuousOn (fun t ↦ meanScalar (gt t)) (Ico 0 T)) :
    normalizedFlowGoal g₀ := by
  letI : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (ClosedSmoothModel 3) M
  let U : ℝ := T / 2
  have hU : 0 < U := by dsimp [U]; linarith
  have hUT : U < T := by dsimp [U]; linarith
  let clamp : ℝ → ℝ := fun t ↦ max 0 (min t U)
  have hclamp : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hclamp_mem (t : ℝ) : clamp t ∈ Ico (0 : ℝ) T :=
    ⟨le_max_left _ _, lt_of_le_of_lt (max_le hU.le (min_le_right _ _)) hUT⟩
  let r : ℝ → ℝ := fun t ↦ meanScalar (gt (clamp t))
  have hr : Continuous r := hmean.comp_continuous hclamp hclamp_mem
  have hr_eq {t : ℝ} (ht : t ∈ Ico 0 U) : r t = meanScalar (gt t) := by
    simp only [r, clamp, min_eq_left ht.2.le, max_eq_right ht.1]
  obtain ⟨S, τ, c, hS, hτ0, hc0, hc, hreach, hdata⟩ := exists_normalizingTimeData hr hU
  refine ⟨S, hS, timeReparameterizedConstRescaling gt τ c hc, ?_, ?_⟩
  · change (gt (τ 0)).constSMul (c 0) (hc 0) = g₀
    simp only [hτ0, hc0, h0]
    cases g₀
    simp [ClosedSmoothRiemannianMetric.constSMul]
  · intro t ht x
    have hτU := hreach ht
    have hτT : τ t ∈ Ico (0 : ℝ) T := ⟨hτU.1, hτU.2.trans hUT⟩
    apply
      isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow_of_baseMeanScale_of_baseDensityIntegrable
        (compactFiniteExtendedChartCover (n := 3) (M := M)) gt τ c hc
        (fun s i ↦ HamiltonReactionCoreReduction.inverseChartDensity_integrable _ _ i)
        (fun s ↦ totalVolume_ne_zero (gt (τ s)))
        (hdata t ht).2.2.1
    · simpa only [hr_eq hτU] using (hdata t ht).2.2.2
    · exact hflow (τ t) hτT x
    · exact timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
        ((hjoint (τ t) hτT x).of_le (by norm_num))

/-- Along the actual unnormalized equation, the logarithmic chart density
has derivative minus scalar curvature. -/
theorem hasDerivAt_log_density_of_ricciFlow [SecondCountableTopology M]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t : ℝ} (i : Fin C.chartCount) (z : C.coordinateDomain i)
    (hflow : IsClosedRicciFlowSolutionAt gt t (C.inverseChart i z))
    (hjoint : MetricEntriesJointContDiffAt gt t (C.inverseChart i z) 3) :
    HasDerivAt (fun s ↦ Real.log (C.inverseChartDensity (gt s) i z))
      (-(gt t).scalarAt (C.inverseChart i z)) t := by
  have htrace := traceMetricVariationAt_timeDeriv_eq_negTwoRicci
    (isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt hflow
      (closedRicciFlowExtensionRegularAt_canonical gt t (C.inverseChart i z)))
  convert HamiltonChartDensityLocalDomination.hasDerivAt_log_inverseChartDensity C gt i z
    (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      (hjoint.of_le (by norm_num))) using 1
  rw [htrace]
  ring

/-- A scalar bound on a finite slab gives a uniform integrable density
majorant by comparison with the initial metric. -/
theorem density_le_initial_of_scalar_bound [SecondCountableTopology M]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {U K : ℝ} (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hflow : ∀ t ∈ Icc (0 : ℝ) U, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t ∈ Icc (0 : ℝ) U, ∀ x : M, MetricEntriesJointContDiffAt gt t x 3)
    (hbound : ∀ t ∈ Icc (0 : ℝ) U, ∀ x : M, ‖(gt t).scalarAt x‖ ≤ K)
    (i : Fin C.chartCount) (z : C.coordinateDomain i)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) U) :
    C.inverseChartDensity (gt t) i z ≤
      Real.exp (K * U) * C.inverseChartDensity (gt 0) i z := by
  have hder (s : ℝ) (hs : s ∈ Icc (0 : ℝ) U) :=
    hasDerivAt_log_density_of_ricciFlow C gt i z
      (hflow s hs _) (hjoint s hs _)
  have hlog := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs ↦ (hder s hs).hasDerivWithinAt)
    (fun s hs ↦ by simpa only [norm_neg] using hbound s hs (C.inverseChart i z))
    (convex_Icc (0 : ℝ) U) (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩) ht
  have hdist : ‖t - 0‖ ≤ U := by simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hlogle : Real.log (C.inverseChartDensity (gt t) i z) ≤
      K * U + Real.log (C.inverseChartDensity (gt 0) i z) := by
    have := (le_abs_self _).trans (hlog.trans (mul_le_mul_of_nonneg_left hdist hK))
    rw [Real.norm_eq_abs] at hlog
    linarith
  have hpos (s : ℝ) : 0 < C.inverseChartDensity (gt s) i z :=
    inverseChartPullbackVolumeDensity_pos (gt s) (C.anchor i) (C.coordinateTargetPoint i z)
  have := Real.exp_le_exp.mpr hlogle
  simpa only [Real.exp_add, Real.exp_log (hpos t), Real.exp_log (hpos 0)] using this

/-- Moving integrals of jointly continuous functions are continuous on a
compact Ricci-flow slab. The density majorant comes from the equation. -/
theorem continuousOn_integral_of_ricciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {U : ℝ} (hU : 0 ≤ U)
    (hflow : ∀ t ∈ Icc (0 : ℝ) U, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t ∈ Icc (0 : ℝ) U, ∀ x : M, MetricEntriesJointContDiffAt gt t x 3)
    (f : ℝ → M → ℝ)
    (hf : ContinuousOn (fun p : ℝ × M ↦ f p.1 p.2) (Icc 0 U ×ˢ univ)) :
    ContinuousOn (fun t ↦ ∫ x, f t x ∂volumeMeasure (gt t)) (Icc 0 U) := by
  letI : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (ClosedSmoothModel 3) M
  let C := compactFiniteExtendedChartCover (n := 3) (M := M)
  have hscalar : ContinuousOn (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2)
      (Icc 0 U ×ˢ univ) :=
    continuousOn_scalarAt_joint_of_metricEntriesJointContDiffAt_three
      (fun p hp ↦ hjoint p.1 hp.1 p.2)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hscalar
  obtain ⟨L, hL⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hf
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) U) (x : M) :
      ‖(gt t).scalarAt x‖ ≤ |B| :=
    (hB (t, x) ⟨ht, mem_univ x⟩).trans (le_abs_self B)
  have hfbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) U) (x : M) :
      ‖f t x‖ ≤ |L| :=
    (hL (t, x) ⟨ht, mem_univ x⟩).trans (le_abs_self L)
  have hfspace (t : ℝ) (ht : t ∈ Icc (0 : ℝ) U) : Continuous (f t) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id) (fun x ↦ ⟨ht, mem_univ x⟩)
  have hftime (x : M) : ContinuousOn (fun t ↦ f t x) (Icc 0 U) :=
    hf.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht ↦ ⟨ht, mem_univ x⟩)
  have hdensity (t : ℝ) (i : Fin C.chartCount) :=
    HamiltonReactionCoreReduction.inverseChartDensity_integrable C (gt t) i
  let D := (FiniteExtendedChartFrameMeasureData.ofDensityIntegrable C gt (Icc 0 U)
    (fun t _ i ↦ hdensity t i)).toDecomposition
  have hcoord (i : Fin C.chartCount) : ContinuousOn
      (fun t ↦ ∫ z : C.coordinateDomain i,
        (rawHausdorffLebesgueScale 3 : ℝ) * C.inverseChartDensity (gt t) i z *
          f t (C.inverseChart i z) ∂coordinateLebesgueMeasure (C.coordinateDomain i)) (Icc 0 U) := by
    apply continuousOn_of_dominated
      (bound := fun z ↦ (‖(rawHausdorffLebesgueScale 3 : ℝ)‖ * Real.exp (|B| * U) * |L|) *
        C.inverseChartDensity (gt 0) i z)
    · intro t ht
      exact ((hdensity t i).aestronglyMeasurable.const_mul _).mul
        (((hfspace t ht).measurable.comp (C.inverseChart_measurable i)).aestronglyMeasurable)
    · intro t ht
      apply Eventually.of_forall
      intro z
      have hd : ‖C.inverseChartDensity (gt t) i z‖ ≤
          Real.exp (|B| * U) * C.inverseChartDensity (gt 0) i z := by
        rw [Real.norm_eq_abs, abs_of_nonneg (C.inverseChartDensity_nonneg (gt t) i z)]
        exact density_le_initial_of_scalar_bound C gt hU (abs_nonneg B)
          hflow hjoint hbound i z ht
      calc
        _ = ‖(rawHausdorffLebesgueScale 3 : ℝ)‖ * ‖C.inverseChartDensity (gt t) i z‖ *
            ‖f t (C.inverseChart i z)‖ := by simp only [norm_mul]
        _ ≤ ‖(rawHausdorffLebesgueScale 3 : ℝ)‖ *
            (Real.exp (|B| * U) * C.inverseChartDensity (gt 0) i z) * |L| := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
                (hfbound t ht _) (norm_nonneg _)
                (mul_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le
                  (C.inverseChartDensity_nonneg (gt 0) i z)))
        _ = _ := by ring
    · exact (hdensity 0 i).const_mul _
    · apply Eventually.of_forall
      intro z
      have hd : ContinuousOn (fun t ↦ C.inverseChartDensity (gt t) i z) (Icc 0 U) := by
        intro t ht
        exact (C.hasDerivAt_inverseChartDensity i z
          (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
            ((hjoint t ht _).of_le (by norm_num)))).continuousAt.continuousWithinAt
      exact (continuousOn_const.mul hd).mul (hftime _)
  have hsum := continuousOn_finsetSum (s := Finset.univ) (fun i _ ↦ hcoord i)
  apply hsum.congr
  intro t ht
  letI := volumeMeasure_isFiniteMeasure (gt t)
  exact (integral_eq_sum_rawHausdorff_coordinateDensity D ht (f t)
    ((hfspace t ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))

/-- Mean scalar curvature is continuous on every compact regular Ricci-flow
slab, using the actual finite volume and scalar integrals. -/
theorem continuousOn_meanScalar_of_ricciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {U : ℝ} (hU : 0 ≤ U)
    (hflow : ∀ t ∈ Icc (0 : ℝ) U, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t ∈ Icc (0 : ℝ) U, ∀ x : M, MetricEntriesJointContDiffAt gt t x 3) :
    ContinuousOn (fun t ↦ meanScalar (gt t)) (Icc 0 U) := by
  have hvolume : ContinuousOn (fun t ↦ totalVolume (gt t)) (Icc 0 U) := by
    have h := continuousOn_integral_of_ricciFlow gt hU hflow hjoint
      (fun _ _ ↦ (1 : ℝ)) continuousOn_const
    simpa [totalVolume, Measure.real] using h
  have hscalar : ContinuousOn (fun t ↦ totalScalar (gt t)) (Icc 0 U) :=
    continuousOn_integral_of_ricciFlow gt hU hflow hjoint
      (fun t x ↦ (gt t).scalarAt x)
      (continuousOn_scalarAt_joint_of_metricEntriesJointContDiffAt_three
        (fun p hp ↦ hjoint p.1 hp.1 p.2))
  exact hscalar.div hvolume (fun t _ ↦ totalVolume_ne_zero (gt t))

/-- Every regular short-time Ricci flow supplies a normalized short-time
flow with the same initial metric. -/
theorem normalization
    (h : ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, regularRicciFlowGoal g₀) :
    ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, normalizedFlowGoal g₀ := by
  intro g₀
  obtain ⟨T, hT, gt, h0, hflow, hjoint⟩ := h g₀
  have hhalf : 0 < T / 2 := by linarith
  have hsub : Icc (0 : ℝ) (T / 2) ⊆ Ico (0 : ℝ) T := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩
  have hflow' := fun t ht x ↦ hflow t (hsub ht) x
  have hjoint' := fun t ht x ↦ hjoint t (hsub ht) x
  exact normalizedFlowGoal_of_continuousOn_meanScalar g₀ gt hhalf h0
    (fun t ht x ↦ hflow' t ⟨ht.1, ht.2.le⟩ x)
    (fun t ht x ↦ hjoint' t ⟨ht.1, ht.2.le⟩ x)
    ((continuousOn_meanScalar_of_ricciFlow gt hhalf.le hflow' hjoint').mono
      (fun _ ht ↦ ⟨ht.1, ht.2.le⟩))

end Manifold

end Poincare.ClosedRicciFlowNormalization
