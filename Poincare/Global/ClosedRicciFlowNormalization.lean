import Poincare.Global.NormalizedFlowRescaling
import Poincare.Global.MetricRescaleFiniteAtlasIntegrals
import Poincare.Global.MetricRescaleFiniteAtlasForwardFlow
import Poincare.Global.HamiltonChartDensityLocalDomination
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

end Manifold

end Poincare.ClosedRicciFlowNormalization
