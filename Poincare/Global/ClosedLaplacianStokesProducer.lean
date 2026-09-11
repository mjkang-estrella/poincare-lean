import Poincare.Global.NormalizedFlowHausdorffPartitionStokes
import Poincare.Global.HamiltonChartDensityLocalDomination

/-!
# Open-chart data for closed Laplacian Stokes

The constructors below supply genuine chart measures and compactly supported
coordinate scalars. Coordinate coefficient identities remain explicit inputs
to the final partial constructor.
-/

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesProducer

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The full inverse-chart measure is the Riemannian measure on its open source. -/
theorem openChart_measure (g : ClosedSmoothRiemannianMetric n M) (p : M) :
    HausdorffChartDensityEquality g (extChartAt I p).target
      (inverseExtendedChartParametrization (n := n) p)
      (extChartAt I p).source (inverseChartPullbackVolumeDensity g p) := by
  have hrange : Set.range (inverseExtendedChartParametrization (n := n) p) =
      (extChartAt I p).source := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (extChartAt I p).map_target z.2
    · intro hx
      refine ⟨⟨extChartAt I p x, (extChartAt I p).map_source hx⟩, ?_⟩
      exact (extChartAt I p).left_inv hx
  simpa only [hrange] using inverseChart_hausdorffChartDensityEquality g p

/-- Finite Riemannian volume gives integrability of the density on the full chart. -/
theorem openChart_density_integrable (g : ClosedSmoothRiemannianMetric n M) (p : M) :
    Integrable (inverseChartPullbackVolumeDensity g p)
      (coordinateLebesgueMeasure (extChartAt I p).target) := by
  have hcont := continuous_inverseChartPullbackVolumeDensity g p
  have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
  have hmeas := (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable
  have hmass := congrArg (fun μ : Measure M ↦ μ univ) (openChart_measure g p)
  dsimp only at hmass
  rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hmass
  have hfinite :
      ∫⁻ z, ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) *
        inverseChartPullbackVolumeDensity g p z)
        ∂(coordinateLebesgueMeasure (extChartAt I p).target) ≠ (⊤ : ℝ≥0∞) := by
    rw [rawHausdorffCoordinateDensityMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hmass
    rw [hmass]
    letI := volumeMeasure_isFiniteMeasure g
    exact measure_ne_top (volumeMeasure g) _
  have hint := (lintegral_ofReal_ne_top_iff_integrable
    (hcont.const_mul (rawHausdorffLebesgueScale n : ℝ)).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ mul_nonneg hscale.le
      (inverseChartPullbackVolumeDensity_pos g p z).le)).mp hfinite
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint

/-- The compact finite chart cover has a smooth subordinate partition. -/
theorem exists_subordinate_partition (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ,
      ρ.IsSubordinate (fun i ↦ (extChartAt I (C.anchor i)).source) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ _
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
  rw [C.sources_cover]

end Poincare.ClosedLaplacianStokesProducer
