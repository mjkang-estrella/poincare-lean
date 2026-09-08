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

end HamiltonReactionCoreReduction
end Poincare
