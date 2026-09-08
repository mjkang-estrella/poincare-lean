import Poincare.Global.ClosedMetricThirdJetTopology
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity
import Poincare.Global.HamiltonReactionCoreReduction

/-!
# Compact-family curvature continuity from scalar third-jet profiles

Coordinate contractions and their intrinsic identities hold for each metric
individually. Their continuity therefore requires only a topological parameter.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonCompactFamilyInvariantContinuity

variable {n : ℕ} {M : Type u} {K : Type v}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [TopologicalSpace K]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Coordinate Ricci jets give joint continuity of intrinsic scalar curvature
for an arbitrary topological parameter space. -/
theorem continuousAt_scalarAt_of_ricciJet
    {metric : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyRicciJetChartContinuousAt metric k₀ x) :
    ContinuousAt (fun p : K × M ↦ (metric p.1).scalarAt p.2) (k₀, x) := by
  classical
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ nhds (extChartAt I x x) := by
    apply hopen.mem_nhds
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hchart :
      ContinuousAt (fun p : K × M ↦ extChartAt I x p.2) (k₀, x) := by
    exact ContinuousAt.comp'
      (f := fun p : K × M ↦ p.2)
      (g := fun y : M ↦ extChartAt I x y)
      (x := (k₀, x)) (continuousAt_extChartAt x) continuousAt_snd
  have hchartPair :
      ContinuousAt
        (fun p : K × M ↦ (p.1, extChartAt I x p.2)) (k₀, x) :=
    continuousAt_fst.prodMk hchart
  have htrace : ContinuousAt
      (fun p : K × E ↦ anchorChartScalarTraceFlow (fun _ : ℝ ↦ metric p.1) x 0 p.2)
      (k₀, extChartAt I x x) := by
    unfold anchorChartScalarTraceFlow
    dsimp only
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (h.inverseCoeff i j).mul
      (h.ricciEntry (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
  have hchartScalar :
      ContinuousAt
        (fun p : K × M ↦
          anchorChartScalarTraceFlow (fun _ : ℝ ↦ metric p.1) x 0 (extChartAt I x p.2))
        (k₀, x) := by
    exact ContinuousAt.comp'
      (f := fun p : K × M ↦ (p.1, extChartAt I x p.2))
      (g := fun p : K × E ↦ anchorChartScalarTraceFlow (fun _ : ℝ ↦ metric p.1) x 0 p.2)
      (x := (k₀, x)) htrace hchartPair
  have hsource :
      ∀ᶠ p : K × M in nhds (k₀, x),
        p.2 ∈ (extChartAt I x).source :=
    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
  have hone :
      ∀ᶠ p : K × M in nhds (k₀, x),
        extChartAt I x p.2 ∈ oneLocus :=
    hchart.eventually hone_mem
  have hEq :
      (fun p : K × M ↦ (metric p.1).scalarAt p.2) =ᶠ[nhds (k₀, x)]
        (fun p : K × M ↦
          anchorChartScalarTraceFlow (fun _ : ℝ ↦ metric p.1) x 0 (extChartAt I x p.2)) := by
    filter_upwards [hsource, hone] with p hpSource hpOne
    have hz : extChartAt I x p.2 ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hpSource
    have hχone :
        ∀ᶠ z' in nhds (extChartAt I x p.2),
          GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    symm
    calc
      anchorChartScalarTraceFlow (fun _ : ℝ ↦ metric p.1) x 0 (extChartAt I x p.2) =
          (metric p.1).scalarAt
            ((extChartAt I x).symm (extChartAt I x p.2)) :=
        anchorChartScalarTraceFlow_eq_scalarAt_zone (fun _ : ℝ ↦ metric p.1) x 0 hz hχone
      _ = (metric p.1).scalarAt p.2 := by
        rw [(extChartAt I x).left_inv hpSource]
  exact hchartScalar.congr_of_eventuallyEq hEq

/-- Coordinate Ricci jets give joint continuity of the intrinsic squared
Ricci norm without a differentiable structure on the parameter. -/
theorem continuousAt_ricciNormSqAt_of_ricciJet
    {metric : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyRicciJetChartContinuousAt metric k₀ x) :
    ContinuousAt (fun p : K × M ↦ (metric p.1).ricciNormSqAt p.2) (k₀, x) := by
  classical
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ nhds (extChartAt I x x) := by
    apply hopen.mem_nhds
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hchart :
      ContinuousAt (fun p : K × M ↦ extChartAt I x p.2) (k₀, x) :=
    ContinuousAt.comp'
      (f := fun p : K × M ↦ p.2)
      (g := fun y : M ↦ extChartAt I x y)
      (x := (k₀, x)) (continuousAt_extChartAt x) continuousAt_snd
  have hchartPair :
      ContinuousAt
        (fun p : K × M ↦ (p.1, extChartAt I x p.2)) (k₀, x) :=
    continuousAt_fst.prodMk hchart
  have hcoord :
      ContinuousAt
        (fun p : K × E ↦ anchorChartRicciNormSqFlow (fun _ : ℝ ↦ metric p.1) x 0 p.2)
        (k₀, extChartAt I x x) :=
    by
      unfold anchorChartRicciNormSqFlow
      dsimp only
      apply tendsto_finsetSum
      intro j _
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro k _
      apply tendsto_finsetSum
      intro l _
      exact (((h.inverseCoeff j k).mul (h.inverseCoeff i l)).mul
        (h.ricciEntry (Module.finBasis ℝ E k) (Module.finBasis ℝ E l))).mul
        (h.ricciEntry (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
  have hchartNorm :
      ContinuousAt
        (fun p : K × M ↦
          anchorChartRicciNormSqFlow (fun _ : ℝ ↦ metric p.1) x 0 (extChartAt I x p.2))
        (k₀, x) :=
    ContinuousAt.comp'
      (f := fun p : K × M ↦ (p.1, extChartAt I x p.2))
      (g := fun p : K × E ↦ anchorChartRicciNormSqFlow (fun _ : ℝ ↦ metric p.1) x 0 p.2)
      (x := (k₀, x)) hcoord hchartPair
  have hsource :
      ∀ᶠ p : K × M in nhds (k₀, x),
        p.2 ∈ (extChartAt I x).source :=
    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
  have hone :
      ∀ᶠ p : K × M in nhds (k₀, x),
        extChartAt I x p.2 ∈ oneLocus :=
    hchart.eventually hone_mem
  have hEq :
      (fun p : K × M ↦ (metric p.1).ricciNormSqAt p.2)
        =ᶠ[nhds (k₀, x)]
      (fun p : K × M ↦
        anchorChartRicciNormSqFlow (fun _ : ℝ ↦ metric p.1) x 0 (extChartAt I x p.2)) := by
    filter_upwards [hsource, hone] with p hpSource hpOne
    have hz : extChartAt I x p.2 ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hpSource
    have hχone :
        ∀ᶠ z' in nhds (extChartAt I x p.2),
          GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    symm
    calc
      anchorChartRicciNormSqFlow (fun _ : ℝ ↦ metric p.1) x 0 (extChartAt I x p.2) =
          (metric p.1).ricciNormSqAt
            ((extChartAt I x).symm (extChartAt I x p.2)) :=
        anchorChartRicciNormSqFlow_eq_ricciNormSqAt_zone
          (fun _ : ℝ ↦ metric p.1) x 0 hz hχone
      _ = (metric p.1).ricciNormSqAt p.2 := by
        rw [(extChartAt I x).left_inv hpSource]
  exact hchartNorm.congr_of_eventuallyEq hEq

section ThirdJetTopology

local instance : TopologicalSpace (ClosedSmoothRiemannianMetric n M) :=
  closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)

/-- Continuity in the landed scalar third-jet topology implies joint scalar
and squared traceless-Ricci continuity. Compactness of the parameter is unnecessary. -/
theorem curvatureContinuity_of_continuous
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hmetric : Continuous metric) :
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
    Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2) := by
  have hj (k : K) (x : M) : MetricFamilyRicciJetChartContinuousAt metric k x :=
    (metricFamilyBlendedMetricEntryThirdJetContinuousAt_of_continuous hmetric k x
      ).toBlendedMetricThirdJetContinuousAt.toRicciJetChartContinuousAt
  have hs : Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨k, x⟩
    exact continuousAt_scalarAt_of_ricciJet (hj k x)
  have hr : Continuous (fun p : K × M ↦ (metric p.1).ricciNormSqAt p.2) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨k, x⟩
    exact continuousAt_ricciNormSqAt_of_ricciJet (hj k x)
  exact ⟨hs, by
    simpa only [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt] using
      hr.sub ((hs.pow 2).div_const (n : ℝ))⟩

end ThirdJetTopology

/-- Joint scalar third-jet profiles supply both curvature-continuity clauses
of the compact-family reaction core, in every dimension and for any parameter space. -/
theorem curvatureContinuity_of_thirdJetProfiles_continuous
    (K : Type v) [TopologicalSpace K]
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
    Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2) := by
  letI : TopologicalSpace (ClosedSmoothRiemannianMetric n M) :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
  exact curvatureContinuity_of_continuous metric
    (continuous_closedMetricFamily_of_entryThirdJetProfileJointContinuous hjet)

end Poincare.HamiltonCompactFamilyInvariantContinuity
