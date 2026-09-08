import Poincare.Global.HamiltonReactionCoreReduction
import Poincare.Global.HausdorffInverseChartGramContinuity
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic

noncomputable section
open Bundle FiberBundle Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
set_option autoImplicit false
universe u v
namespace Poincare.HamiltonChartDensityLocalDomination

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

end Poincare.HamiltonChartDensityLocalDomination
