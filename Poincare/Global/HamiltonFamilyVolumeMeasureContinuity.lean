import Poincare.Global.HamiltonCompactFamilyInvariantContinuity
import Poincare.Global.HamiltonReactionCoreReduction
import Poincare.Global.HausdorffInverseChartGramContinuity
import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonFamilyVolumeMeasureContinuity

variable {n : ℕ} {M : Type u} {K : Type v}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [TopologicalSpace K]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/-- Value profiles at their own anchor give continuous intrinsic pairings
at each fixed manifold point and pair of tangent vectors. -/
theorem continuous_inner_of_thirdJetProfiles_continuous
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (a b : E) :
    Continuous (fun k ↦ (metric k).inner x a b) := by
  have h := (hjet (.value x a b)).comp
    (continuous_id.prodMk (continuous_const (y := extChartAt I x x)))
  simpa only [Function.comp_def, id_eq, metricEntryThirdJetProfile_value_anchor] using h

variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The pullback Gram matrix is continuous in the parameter at every genuine
coordinate, including coordinates outside the anchor's cutoff support. -/
theorem continuous_parameter_inverseChartPullbackGramMatrix
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (z : (extChartAt I x).target) :
    Continuous (fun k ↦ inverseChartPullbackGramMatrix (metric k) x z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_inner_of_thirdJetProfiles_continuous metric hjet _ _ _

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Every inverse-chart volume density is continuous in the metric parameter. -/
theorem continuous_parameter_inverseChartPullbackVolumeDensity
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (z : (extChartAt I x).target) :
    Continuous (fun k ↦ inverseChartPullbackVolumeDensity (metric k) x z) := by
  exact VolumeDensity.continuous_chartVolumeDensity
    (continuous_parameter_inverseChartPullbackGramMatrix metric hjet x z)

/-- On a fixed coordinate set where the anchor cutoff is one, the genuine
volume density is jointly continuous in the metric parameter and coordinate. -/
theorem continuous_inverseChartPullbackVolumeDensity_on_cutoffOne
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2))
    (x : M) (S : Set E) (hS : S ⊆ (extChartAt I x).target)
    (hχ : ∀ z ∈ S, GeodesicTransport.cutoff (n := n) x z = 1) :
    Continuous (fun p : K × S ↦ inverseChartPullbackVolumeDensity
      (metric p.1) x ⟨p.2.1, hS p.2.2⟩) := by
  apply VolumeDensity.continuous_chartVolumeDensity
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hp : Continuous (fun p : K × S ↦ (p.1, (p.2 : E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h := (hjet (.value x (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))).comp hp
  apply h.congr
  intro p
  rw [inverseChartPullbackGramMatrix_eq_field]
  change CovariantDerivative.blendedChartMetric
      (GeodesicTransport.cutoff (n := n) x)
      (GeodesicTransport.backgroundMetric (n := n)) (metric p.1).inner x p.2.1 _ _ =
    CovariantDerivative.chartMetric (metric p.1).inner x p.2.1 _ _
  rw [CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    _ _ _ _ (hχ p.2.1 p.2.2)]

end Poincare.HamiltonFamilyVolumeMeasureContinuity
