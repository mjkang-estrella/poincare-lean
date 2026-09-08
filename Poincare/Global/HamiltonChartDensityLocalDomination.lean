import Poincare.Global.HamiltonReactionCoreReduction
import Poincare.Global.HausdorffInverseChartGramContinuity
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic

noncomputable section
open Bundle FiberBundle Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
set_option autoImplicit false
universe u v
namespace Poincare.HamiltonChartDensityLocalDomination

section DimensionGeneral

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [ConnectedSpace M] in
/-- The intrinsic time-variation trace is jointly continuous. -/
theorem continuous_trace_timeDeriv
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    Continuous (fun p : ℝ × M ↦
      traceMetricVariationAt (gt p.1) (timeDerivAt gt p.1) p.2) := by
  classical
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  have hchart : ContinuousAt (fun p : ℝ × M ↦
      (p.1, extChartAt I x p.2)) (t, x) :=
    continuousAt_fst.prodMk (ContinuousAt.comp' (f := fun p : ℝ × M ↦ p.2)
      (g := fun y ↦ extChartAt I x y) (continuousAt_extChartAt x) continuousAt_snd)
  have hsource : ∀ᶠ p : ℝ × M in 𝓝 (t, x),
      p.2 ∈ (extChartAt I x).source :=
    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
  have hentry (i j : Fin (Module.finrank ℝ (TM x))) :
      ContinuousAt (fun p : ℝ × M ↦ gramMatrix (gt p.1) x p.2 i j) (t, x) := by
    have hc := ContinuousAt.comp' (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
      ((hjoint t x (b i) (b j)).continuousAt) hchart
    apply hc.congr_of_eventuallyEq
    filter_upwards [hsource] with p hp
    dsimp only [metricEntryJointChart]
    rw [(extChartAt I x).left_inv hp]
    rfl
  have hvariation (i j : Fin (Module.finrank ℝ (TM x))) :
      ContinuousAt (fun p : ℝ × M ↦
        timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j)) (t, x) := by
    have hc := ContinuousAt.comp' (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
      (continuousAt_joint_timeDeriv_of_joint_contDiffAt_one
      (fun τ z ↦ metricEntryJointChart gt x (b i) (b j) (τ, z))
      t (extChartAt I x x) ((hjoint t x (b i) (b j)).of_le (by norm_num))) hchart
    apply hc.congr_of_eventuallyEq
    filter_upwards [hsource] with p hp
    dsimp only [metricEntryJointChart]
    rw [(extChartAt I x).left_inv hp]
    rfl
  let G := fun p : ℝ × M ↦ gramMatrix (gt p.1) x p.2
  have hG : ContinuousAt G (t, x) :=
    continuousAt_pi.mpr fun i ↦ continuousAt_pi.mpr fun j ↦ hentry i j
  have hdet : (G (t, x)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (gramMatrix_at_base_isUnit (g := gt t) (x := x)))
  have hinv : ContinuousAt (fun p ↦ (G p)⁻¹) (t, x) := by
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using
      ((continuous_id.matrix_det.continuousAt.comp hG).inv₀ hdet).smul (continuous_id.matrix_adjugate.continuousAt.comp hG)
  have hunit : ∀ᶠ p in 𝓝 (t, x), IsUnit (G p) := by
    filter_upwards [(continuous_id.matrix_det.continuousAt.comp hG).eventually_ne hdet] with p hp
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp)
  have hsum : ContinuousAt (fun p : ℝ × M ↦
      ∑ i, ∑ j, (G p)⁻¹ i j *
        timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j)) (t, x) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((continuousAt_pi.mp (continuousAt_pi.mp hinv i) j)).mul (hvariation i j)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hunit] with p hp
  exact traceMetricVariationAt_eq_sum_gram_inv (gt p.1) (timeDerivAt gt p.1) x p.2 hp
    (timeDerivBilinAt gt p.1 p.2
      (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
        ((hjoint p.1 p.2).of_le (by norm_num)))) (by intro a c; rfl)

/-- Taking the logarithm cancels the coordinate density from its first variation. -/
theorem hasDerivAt_log_inverseChartDensity
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    {t : ℝ} (i : Fin C.chartCount) (z : C.coordinateDomain i)
    (htime : TimeDifferentiableAt gt t (C.inverseChart i z)) :
    HasDerivAt (fun τ ↦ Real.log (C.inverseChartDensity (gt τ) i z))
      ((1 / 2 : ℝ) * traceMetricVariationAt (gt t) (timeDerivAt gt t)
        (C.inverseChart i z)) t := by
  have hpos : 0 < C.inverseChartDensity (gt t) i z :=
    inverseChartPullbackVolumeDensity_pos (gt t) (C.anchor i) (C.coordinateTargetPoint i z)
  convert (C.hasDerivAt_inverseChartDensity i z htime).log hpos.ne' using 1
  field_simp

/-- An intrinsic trace bound controls density ratios on a unit time strip. -/
theorem inverseChartDensity_le_exp_mul
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (t K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ τ ∈ Icc (t - 1) (t + 1), ∀ x : M,
      ‖(1 / 2 : ℝ) * traceMetricVariationAt (gt τ) (timeDerivAt gt τ) x‖ ≤ K)
    (i : Fin C.chartCount) (z : C.coordinateDomain i)
    {τ : ℝ} (hτ : τ ∈ Icc (t - 1) (t + 1)) :
    C.inverseChartDensity (gt τ) i z ≤ Real.exp K * C.inverseChartDensity (gt t) i z := by
  have hderiv (s : ℝ) := hasDerivAt_log_inverseChartDensity C gt i z
    (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hjoint s (C.inverseChart i z)).of_le (by norm_num)))
  have hlog := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ Icc (t - 1) (t + 1)) ↦ (hderiv s).hasDerivWithinAt)
    (fun s hs ↦ hbound s hs (C.inverseChart i z)) (convex_Icc (t - 1) (t + 1))
    (show t ∈ Icc (t - 1) (t + 1) by constructor <;> linarith) hτ
  have hdist : ‖τ - t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hτ.1, hτ.2]
  have hlogle : Real.log (C.inverseChartDensity (gt τ) i z) ≤
      K + Real.log (C.inverseChartDensity (gt t) i z) := by
    have := le_trans (le_abs_self _) (le_trans hlog (mul_le_mul_of_nonneg_left hdist hK))
    rw [mul_one] at this
    linarith
  have hpos (s : ℝ) : 0 < C.inverseChartDensity (gt s) i z :=
    inverseChartPullbackVolumeDensity_pos (gt s) (C.anchor i) (C.coordinateTargetPoint i z)
  have := Real.exp_le_exp.mpr hlogle
  simpa only [Real.exp_add, Real.exp_log (hpos τ), Real.exp_log (hpos t)] using this

end DimensionGeneral

section DimensionThree
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

omit [SimplyConnectedSpace M] in
/-- Compactness and joint metric entries supply the local integrable envelope. -/
theorem localBound_of_jointMetricEntries
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    let C := compactFiniteExtendedChartCover (n := 3) (M := M)
    ∀ t : ℝ, ∃ s ∈ 𝓝 t,
      ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
        (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
        (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
          ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z) := by
  classical
  intro C t
  have hcont := (continuous_trace_timeDeriv gt hjoint).const_mul (1 / 2 : ℝ)
  obtain ⟨L, hL⟩ := ((isCompact_Icc : IsCompact (Icc (t - 1) (t + 1))).prod
    (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hcont.continuousOn
  let K := max L 0
  have hK : 0 ≤ K := le_max_right _ _
  have hbound (τ : ℝ) (hτ : τ ∈ Icc (t - 1) (t + 1)) (x : M) :
      ‖(1 / 2 : ℝ) * traceMetricVariationAt (gt τ) (timeDerivAt gt τ) x‖ ≤ K :=
    (hL (τ, x) ⟨hτ, mem_univ x⟩).trans (le_max_left _ _)
  refine ⟨Icc (t - 1) (t + 1), Icc_mem_nhds (by linarith) (by linarith),
    fun i z ↦ (K * Real.exp K) * C.inverseChartDensity (gt t) i z, ?_, ?_⟩
  · intro i
    exact (HamiltonReactionCoreReduction.inverseChartDensity_integrable C (gt t) i).const_mul _
  · intro i
    apply Eventually.of_forall
    intro z τ hτ
    have hdensity := inverseChartDensity_le_exp_mul C gt hjoint t K hK hbound i z hτ
    have hnonneg := C.inverseChartDensity_nonneg (gt τ) i z
    calc
      ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ =
          C.inverseChartDensity (gt τ) i z *
            ‖(1 / 2 : ℝ) * traceMetricVariationAt (gt τ) (timeDerivAt gt τ)
              (C.inverseChart i z)‖ := by
        unfold finiteExtendedChartFrameDensityDerivative
        rw [show (1 / 2 : ℝ) * C.inverseChartDensity (gt τ) i z *
            traceMetricVariationAt (gt τ) (timeDerivAt gt τ) (C.inverseChart i z) =
            C.inverseChartDensity (gt τ) i z * ((1 / 2 : ℝ) *
              traceMetricVariationAt (gt τ) (timeDerivAt gt τ) (C.inverseChart i z)) by ring]
        rw [norm_mul, Real.norm_of_nonneg hnonneg]
      _ ≤ C.inverseChartDensity (gt τ) i z * K :=
        mul_le_mul_of_nonneg_left (hbound τ hτ _) hnonneg
      _ ≤ (Real.exp K * C.inverseChartDensity (gt t) i z) * K :=
        mul_le_mul_of_nonneg_right hdensity hK
      _ = (K * Real.exp K) * C.inverseChartDensity (gt t) i z := by ring

end DimensionThree

end Poincare.HamiltonChartDensityLocalDomination
