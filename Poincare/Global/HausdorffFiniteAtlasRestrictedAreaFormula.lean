import Poincare.Global.HausdorffInverseChartAreaFormula
import Poincare.Global.HausdorffFiniteAtlasChartFrameReduction

/-!
# Restricted finite-atlas inverse-chart area formula

The exact area formula on a full genuine inverse-chart target restricts to
every measurable disjointized coordinate piece.  The inclusion is an
isometry for the two pullback metrics, while the raw coordinate-density
measure maps to the corresponding restriction.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

namespace FiniteExtendedChartCover

/-- The pullback Hausdorff area formula on every restricted coordinate
piece of a finite genuine inverse atlas is automatic. -/
theorem restrictedInverseChartPullbackHausdorffAreaFormula
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin C.chartCount) :
    C.RestrictedInverseChartPullbackHausdorffAreaFormula g i := by
  rw [RestrictedInverseChartPullbackHausdorffAreaFormula,
    PullbackMetricHausdorffDensityFormula]
  let T : Set E := (extChartAt I (C.anchor i)).target
  let V : Set E := C.coordinateDomain i
  have hVT : V ⊆ T := C.coordinateDomain_subset_target i
  let ι : V → T := Set.inclusion hVT
  let ψT : T → M := inverseExtendedChartParametrization
    (n := n) (M := M) (C.anchor i)
  let ψV : V → M := C.inverseChart i
  letI : MetricSpace M := g.toMetricSpace
  let hψT : Topology.IsEmbedding ψT :=
    inverseExtendedChartParametrization_isEmbedding
      (n := n) (M := M) (C.anchor i)
  let hψV : Topology.IsEmbedding ψV := C.inverseChart_isEmbedding i
  let pullbackMetricT : MetricSpace T := hψT.comapMetricSpace ψT
  let pullbackEMetricT : EMetricSpace T :=
    @MetricSpace.toEMetricSpace T pullbackMetricT
  let pullbackMetricV : MetricSpace V := hψV.comapMetricSpace ψV
  let pullbackEMetricV : EMetricSpace V :=
    @MetricSpace.toEMetricSpace V pullbackMetricV
  let μT : Measure T := rawHausdorffCoordinateDensityMeasure T
    (inverseChartPullbackVolumeDensity g (C.anchor i))
  let μV : Measure V := rawHausdorffCoordinateDensityMeasure V
    (C.inverseChartDensity g i)
  letI : EMetricSpace T := pullbackEMetricT
  letI : PseudoEMetricSpace T := pullbackEMetricT.toPseudoEMetricSpace
  letI : EMetricSpace V := pullbackEMetricV
  letI : PseudoEMetricSpace V := pullbackEMetricV.toPseudoEMetricSpace
  change (μH[(n : ℝ)] : Measure V) = μV

  have hTmeas : MeasurableSet T :=
    (isOpen_extChartAt_target (C.anchor i)).measurableSet
  have hVmeas : MeasurableSet V := C.coordinateDomain_measurable i
  have hιEmbedding : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.inclusion hVT
  have hRangeMeas : MeasurableSet (Set.range ι) := by
    rw [Set.range_inclusion]
    exact hVmeas.preimage measurable_subtype_coe
  have hιMeas : MeasurableEmbedding ι :=
    hιEmbedding.measurableEmbedding hRangeMeas
  have hψcomp : ψV = ψT ∘ ι := by
    funext z
    rfl
  have hιIso : Isometry ι := by
    intro x y
    rfl
  have hfull :
      (μH[(n : ℝ)] : Measure T) = μT := by
    simpa only [InverseChartPullbackHausdorffAreaFormula,
      PullbackMetricHausdorffDensityFormula, T, ψT, hψT, pullbackMetricT,
      pullbackEMetricT, μT] using
      (inverseChartPullbackHausdorffAreaFormula g (C.anchor i))
  have hraw : Measure.map ι μV = μT.restrict (Set.range ι) := by
    simpa only [ι, μV, μT, V, T, inverseChartDensity,
      coordinateTargetPoint] using
      (map_rawHausdorffCoordinateDensityMeasure_inclusion
        hTmeas hVmeas hVT
        (inverseChartPullbackVolumeDensity g (C.anchor i)))
  apply hιMeas.map_injective
  rw [hιIso.map_hausdorffMeasure
      (Or.inl (by positivity : (0 : ℝ) ≤ n)), hfull]
  exact hraw.symm

end FiniteExtendedChartCover

/-- Build the finite inverse-atlas measure package from density
integrability alone.  The chartwise area formulas are now theorems rather
than input data. -/
def FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (s : Set ℝ)
    (hDensity : ∀ t ∈ s, ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt t) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i))) :
    FiniteExtendedChartFrameMeasureData C gt s where
  density_integrable := hDensity
  areaFormula := fun t _ht i ↦
    C.restrictedInverseChartPullbackHausdorffAreaFormula (gt t) i

/-- The local Hausdorff chart-density identity on every disjointized finite
atlas piece, with no area-formula hypothesis. -/
theorem FiniteExtendedChartCover.hausdorffChartDensityEquality
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin C.chartCount) :
    HausdorffChartDensityEquality g (C.coordinateDomain i)
      (C.inverseChart i) (C.manifoldPiece i)
      (C.inverseChartDensity g i) :=
  C.hausdorffChartDensityEquality_of_restrictedAreaFormula g i
    (C.restrictedInverseChartPullbackHausdorffAreaFormula g i)

/-- Build the corrected global chart-frame variation package from raw
density integrability and the existing analytic domination data.  No
area-formula witness is present in this interface. -/
def GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (timeSet : ℝ → Set ℝ)
    (hDensity : ∀ t : ℝ, ∀ τ ∈ timeSet t,
      ∀ i : Fin C.chartCount,
        Integrable (C.inverseChartDensity (gt τ) i)
          (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hDomination : ∀ t : ℝ,
      FiniteExtendedChartFrameDensityDominationAt
        C gt (timeSet t) t) :
    GlobalFiniteExtendedChartFrameDensityData C gt where
  timeSet := timeSet
  measureData t :=
    FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
      C gt (timeSet t) (hDensity t)
  domination := hDomination

/-- Legacy selected-basis data on a finite inverse atlas, with the proved
area formula removed from the input surface.  The remaining
`coordinateGramDensity` field is intentionally explicit: it identifies the
honest inverse-chart frame with the repository's independent
`Module.finBasis` convention and is not a consequence of the area theorem. -/
structure GlobalFiniteExtendedChartDensityData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  timeSet : ℝ → Set ℝ
  density_integrable : ∀ t : ℝ, ∀ τ ∈ timeSet t,
    ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt τ) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i))
  domination : ∀ t : ℝ,
    FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t
  coordinateGramDensity : ∀ τ : ℝ, ∀ i : Fin C.chartCount,
    ∀ z : C.coordinateDomain i,
      C.inverseChartDensity (gt τ) i z =
        ClosedSmoothRiemannianMetric.coordinateGramVolumeDensityAt
          gt (C.inverseChart i z) τ

/-- The finite-atlas density, domination, and independent frame
identification construct exactly the global Hausdorff chart-density
variation consumed by the legacy fully assembled energy endpoint. -/
def GlobalFiniteExtendedChartDensityData.toChartDensityVariation
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteExtendedChartDensityData C gt) :
    GlobalFiniteHausdorffChartDensityVariation gt := by
  let measureData : ∀ t : ℝ,
      FiniteExtendedChartFrameMeasureData C gt (H.timeSet t) :=
    fun t ↦ FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
      C gt (H.timeSet t) (H.density_integrable t)
  exact
    { timeSet := H.timeSet
      decomposition := fun t ↦ (measureData t).toDecomposition
      differentiation := fun t ↦
        (H.domination t).toDominatedDifferentiation (measureData t)
      usesCoordinateGramDensity := fun _t τ i z ↦
        H.coordinateGramDensity τ i z
      timeDifferentiable := fun t i z ↦
        (H.domination t).timeDifferentiable i z t
          (mem_of_mem_nhds (H.domination t).timeSet_mem) }

/-- Forgetting the independent selected-basis identification gives the
corrected chart-frame variation package. -/
def GlobalFiniteExtendedChartDensityData.toChartFrameDensityVariation
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteExtendedChartDensityData C gt) :
    GlobalFiniteHausdorffChartFrameDensityVariation gt :=
  (GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable
    C gt H.timeSet H.density_integrable H.domination).toChartFrameDensityVariation

end Poincare
