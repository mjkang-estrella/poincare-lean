import Poincare.Global.HamiltonReactionEndpoint
import Poincare.Global.HamiltonFiniteEnergyFlowInterface
import Poincare.Global.HausdorffInverseChartGramContinuity

/-!
# Reducing the chart-density inputs of the Hamilton reaction record

The area formula and finite manifold volume give integrability on each
selected chart piece. Joint metric regularity removes the separate time
and density-derivative measurability inputs. Local integrable domination
and compact-family continuity remain explicit obligations.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal
universe u v
namespace Poincare
namespace HamiltonReactionCoreReduction

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/-- Finite volume and the proved chart area formula make every restricted
inverse-chart density integrable, even when its coordinate piece is not compact. -/
theorem inverseChartDensity_integrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M) (i : Fin C.chartCount) :
    Integrable (C.inverseChartDensity g i)
      (coordinateLebesgueMeasure (C.coordinateDomain i)) := by
  have hcont : Continuous (C.inverseChartDensity g i) :=
    (continuous_inverseChartPullbackVolumeDensity g (C.anchor i)).comp
      (continuous_subtype_val.subtype_mk fun z ↦ C.coordinateDomain_subset_target i z.2)
  have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (MeasureTheory.Measure.hausdorffMeasure
        (Module.finrank ℝ (ClosedSmoothModel n) : ℝ))
      (volume : Measure (ClosedSmoothModel n))
  have hmass := congrArg (fun μ : Measure M ↦ μ univ)
    (C.hausdorffChartDensityEquality g i)
  dsimp only at hmass
  rw [Measure.map_apply (C.inverseChart_measurable i) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hmass
  have hfinite :
      ∫⁻ z, ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) *
        C.inverseChartDensity g i z)
        ∂(coordinateLebesgueMeasure (C.coordinateDomain i)) ≠ (⊤ : ℝ≥0∞) := by
    rw [rawHausdorffCoordinateDensityMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hmass
    rw [hmass]
    letI := volumeMeasure_isFiniteMeasure g
    exact measure_ne_top (volumeMeasure g) _
  have hint := (lintegral_ofReal_ne_top_iff_integrable
    (hcont.const_mul (rawHausdorffLebesgueScale n : ℝ)).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ mul_nonneg hscale.le
      (C.inverseChartDensity_nonneg g i z))).mp hfinite
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint

/-- The explicit density derivative is measurable as a pointwise limit of
measurable difference quotients; no joint continuity on a chart closure is needed. -/
theorem densityDerivative_measurable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (t : ℝ) (i : Fin C.chartCount) :
    Measurable (finiteExtendedChartFrameDensityDerivative C gt t i) := by
  have hcont (s : ℝ) : Continuous (C.inverseChartDensity (gt s) i) :=
    (continuous_inverseChartPullbackVolumeDensity (gt s) (C.anchor i)).comp
      (continuous_subtype_val.subtype_mk fun z ↦ C.coordinateDomain_subset_target i z.2)
  let step : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hstep : Tendsto step atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k ↦ by change 0 < 1 / ((k : ℝ) + 1); positivity⟩
  apply measurable_of_tendsto_metrizable
    (f := fun k z ↦ (step k)⁻¹ *
      (C.inverseChartDensity (gt (t + step k)) i z - C.inverseChartDensity (gt t) i z))
  · intro k
    exact ((hcont _).sub (hcont _)).measurable.const_mul _
  · apply tendsto_pi_nhds.mpr
    intro z
    have htime : TimeDifferentiableAt gt t (C.inverseChart i z) :=
      timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
        ((hJoint t (C.inverseChart i z)).of_le (by norm_num))
    exact (C.hasDerivAt_inverseChartDensity i z htime).tendsto_slope_zero_right.comp hstep

/-- Only a local integrable bound remains in the chart-frame record once
joint metric regularity is supplied. -/
theorem chartFrameDensityData_of_joint_of_local_bound
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hBound : let C := compactFiniteExtendedChartCover (n := n) (M := M)
      ∀ t : ℝ, ∃ s ∈ 𝓝 t,
        ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
          (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
          (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
            ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z)) :
    Nonempty (CompactFiniteAtlasChartFrameDensityData gt) := by
  classical
  let C := compactFiniteExtendedChartCover (n := n) (M := M)
  change ∀ t : ℝ, ∃ s ∈ 𝓝 t,
    ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
      (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
      (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
        ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z) at hBound
  choose s hs B hB hbound using hBound
  refine ⟨{
    timeSet := s
    measureData := fun t ↦ FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
      C gt (s t) (fun τ _ i ↦ inverseChartDensity_integrable C (gt τ) i)
    domination := fun t ↦ {
      timeSet_mem := hs t
      densityDerivative_aestronglyMeasurable_at := fun i ↦
        (densityDerivative_measurable C gt hJoint t i).aestronglyMeasurable
      dominatingFunction := B t
      dominatingFunction_integrable := hB t
      densityDerivative_bound := hbound t
      timeDifferentiable := fun i z τ _ ↦
        timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
          ((hJoint τ (C.inverseChart i z)).of_le (by norm_num)) } }⟩

end HamiltonReactionCoreReduction
end Poincare
