import Poincare.Global.CoordinateVolumeDensityVariation
import Poincare.Global.NormalizedFlowVolumeVariation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Hausdorff measure to coordinate-density boundary

The repository defines Riemannian volume using Mathlib's raw Hausdorff measure
`μH[n]`.  On Euclidean space this is a Haar measure, hence it is a fixed scalar
multiple of Lebesgue volume.  That scalar is not definitionally one: Mathlib's
separately normalized Euclidean Hausdorff measure is the construction that is
proved equal to Euclidean volume.  This file keeps the raw-Hausdorff scalar
explicit.

Mathlib proves exact preservation of Hausdorff measure by isometries and
one-sided estimates for Lipschitz maps.  It does not currently provide the
area formula identifying the path-metric Hausdorff measure of a variable
Riemannian metric with `sqrt(det G)` times coordinate Lebesgue measure.
Accordingly, `HausdorffChartDensityEquality` below is the single local equality
left as geometric input.  Everything after that equality--finite measurable
partition, coordinate integration, dominated differentiation, and summation--
is proved here.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Set Filter Metric
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

/-- The fixed Haar normalization relating raw `n`-dimensional Hausdorff
measure on the Euclidean model to Lebesgue volume. -/
noncomputable def rawHausdorffLebesgueScale (n : ℕ) : ℝ≥0 :=
  Measure.addHaarScalarFactor
    (μH[(Module.finrank ℝ (ClosedSmoothModel n) : ℝ)] :
      Measure (ClosedSmoothModel n))
    (volume : Measure (ClosedSmoothModel n))

/-- Raw Hausdorff measure on the Euclidean model is the fixed Haar scalar
times Lebesgue volume. -/
theorem hausdorffMeasure_closedSmoothModel_eq_scale_smul_volume (n : ℕ) :
    (μH[(n : ℝ)] : Measure (ClosedSmoothModel n)) =
      (rawHausdorffLebesgueScale n : ℝ≥0∞) •
        (volume : Measure (ClosedSmoothModel n)) := by
  simpa [rawHausdorffLebesgueScale, ClosedSmoothModel,
    finrank_euclideanSpace] using
    (Measure.isAddLeftInvariant_eq_smul
      (μH[(Module.finrank ℝ (ClosedSmoothModel n) : ℝ)] :
        Measure (ClosedSmoothModel n))
      (volume : Measure (ClosedSmoothModel n)))

/-- Lebesgue measure pulled back to a measurable coordinate domain. -/
noncomputable def coordinateLebesgueMeasure
    (U : Set (ClosedSmoothModel n)) : Measure U :=
  Measure.comap ((↑) : U → ClosedSmoothModel n)
    (volume : Measure (ClosedSmoothModel n))

/-- The raw-Hausdorff-normalized coordinate measure with density `δ`.

For a Riemannian chart, `δ` is intended to be `sqrt |det G|`. -/
noncomputable def rawHausdorffCoordinateDensityMeasure
    (U : Set (ClosedSmoothModel n)) (δ : U → ℝ) : Measure U :=
  (coordinateLebesgueMeasure U).withDensity fun z =>
    ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) * δ z)

/-- The one local geometric equality needed to identify the repo's
Hausdorff-defined measure with a coordinate Gram density. -/
def HausdorffChartDensityEquality
    (g : ClosedSmoothRiemannianMetric n M)
    (U : Set (ClosedSmoothModel n)) (ψ : U → M) (V : Set M)
    (δ : U → ℝ) : Prop :=
  Measure.map ψ (rawHausdorffCoordinateDensityMeasure U δ) =
    (volumeMeasure g).restrict V

/-- On a measurable coordinate domain, raw Hausdorff measure itself is the
scaled pullback of Lebesgue measure. -/
theorem hausdorffMeasure_subtype_eq_scale_smul_coordinateLebesgue
    {U : Set (ClosedSmoothModel n)} (hU : MeasurableSet U) :
    (μH[(n : ℝ)] : Measure U) =
      (rawHausdorffLebesgueScale n : ℝ≥0∞) •
        coordinateLebesgueMeasure U := by
  let hcoe : MeasurableEmbedding ((↑) : U → ClosedSmoothModel n) :=
    MeasurableEmbedding.subtype_coe hU
  apply hcoe.map_injective
  rw [Measure.map_smul]
  rw [coordinateLebesgueMeasure, map_comap_subtype_coe hU]
  rw [isometry_subtype_coe.map_hausdorffMeasure (Or.inl (by positivity))]
  rw [Subtype.range_coe]
  rw [hausdorffMeasure_closedSmoothModel_eq_scale_smul_volume n]
  rw [Measure.restrict_smul]

/-- Exact local identification supplied by Mathlib in the special case where
the coordinate parametrization is genuinely isometric.  Here the Gram density
is `1`; for variable Riemannian coefficients, the missing area formula is
precisely `HausdorffChartDensityEquality`. -/
theorem hausdorffChartDensityEquality_one_of_isometry
    {U : Set (ClosedSmoothModel n)} (hU : MeasurableSet U)
    (g : ClosedSmoothRiemannianMetric n M) (ψ : U → M)
    (hψ : letI : MetricSpace M := g.toMetricSpace; Isometry ψ) :
    HausdorffChartDensityEquality g U ψ (Set.range ψ) (fun _ => 1) := by
  letI : MetricSpace M := g.toMetricSpace
  rw [HausdorffChartDensityEquality]
  have hsource :
      rawHausdorffCoordinateDensityMeasure U (fun _ => 1) =
        (μH[(n : ℝ)] : Measure U) := by
    rw [rawHausdorffCoordinateDensityMeasure]
    simp only [mul_one, ENNReal.ofReal_coe_nnreal]
    rw [withDensity_const]
    exact (hausdorffMeasure_subtype_eq_scale_smul_coordinateLebesgue hU).symm
  rw [hsource]
  simpa [volumeMeasure] using
    hψ.map_hausdorffMeasure (Or.inl (by positivity : (0 : ℝ) ≤ n))

/-- The mass of a coordinate-density measure is the `ofReal` of the
corresponding scaled Lebesgue integral. -/
theorem rawHausdorffCoordinateDensityMeasure_univ_eq_ofReal_integral
    {U : Set (ClosedSmoothModel n)} {δ : U → ℝ}
    (hδ : Integrable δ (coordinateLebesgueMeasure U))
    (hδnonneg : 0 ≤ᵐ[coordinateLebesgueMeasure U] δ) :
    rawHausdorffCoordinateDensityMeasure U δ Set.univ =
      ENNReal.ofReal
        (∫ z : U, (rawHausdorffLebesgueScale n : ℝ) * δ z
          ∂(coordinateLebesgueMeasure U)) := by
  rw [rawHausdorffCoordinateDensityMeasure]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact hδ.const_mul (rawHausdorffLebesgueScale n : ℝ)
  · exact hδnonneg.mono fun z hz => mul_nonneg (by positivity) hz

/-- A finite measurable partition by coordinate charts, carrying the sole
local measure equality and the elementary integrability needed to take real
coordinate integrals. -/
structure FiniteHausdorffChartDensityDecomposition
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (s : Set ℝ) where
  chartCount : ℕ
  coordinateDomain : Fin chartCount → Set (ClosedSmoothModel n)
  coordinateDomain_measurable : ∀ i, MeasurableSet (coordinateDomain i)
  inverseChart : (i : Fin chartCount) → coordinateDomain i → M
  inverseChart_measurable : ∀ i, Measurable (inverseChart i)
  manifoldPiece : Fin chartCount → Set M
  manifoldPiece_measurable : ∀ i, MeasurableSet (manifoldPiece i)
  pieces_pairwise : Set.univ.PairwiseDisjoint manifoldPiece
  pieces_cover : (⋃ i, manifoldPiece i) = Set.univ
  density : ℝ → (i : Fin chartCount) → coordinateDomain i → ℝ
  density_nonneg : ∀ t ∈ s, ∀ i,
    0 ≤ᵐ[coordinateLebesgueMeasure (coordinateDomain i)] density t i
  density_integrable : ∀ t ∈ s, ∀ i,
    Integrable (density t i) (coordinateLebesgueMeasure (coordinateDomain i))
  chartMeasure : ∀ t ∈ s, ∀ i,
    HausdorffChartDensityEquality (gt t)
      (coordinateDomain i) (inverseChart i) (manifoldPiece i) (density t i)

/-- The decomposition's scalar density is the pointwise Gram density already
differentiated in `CoordinateVolumeDensityVariation`. -/
def FiniteHausdorffChartDensityDecomposition.UsesCoordinateGramDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s) : Prop :=
  ∀ t i z,
    D.density t i z =
      ClosedSmoothRiemannianMetric.coordinateGramVolumeDensityAt
        gt (D.inverseChart i z) t

/-- Once a chart decomposition uses the proved Gram density, its pointwise
time derivative is one-half density times the intrinsic metric-speed trace. -/
theorem FiniteHausdorffChartDensityDecomposition.hasDerivAt_density_of_coordinateGram
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (hcoord : D.UsesCoordinateGramDensity)
    {t : ℝ} (i : Fin D.chartCount) (z : D.coordinateDomain i)
    (hgt : TimeDifferentiableAt gt t (D.inverseChart i z)) :
    HasDerivAt (fun τ => D.density τ i z)
      ((1 / 2 : ℝ) * D.density t i z *
        traceMetricVariationAt (gt t) (timeDerivAt gt t)
          (D.inverseChart i z)) t := by
  rw [show (fun τ => D.density τ i z) =
      ClosedSmoothRiemannianMetric.coordinateGramVolumeDensityAt
        gt (D.inverseChart i z) by
    funext τ
    exact hcoord τ i z]
  rw [hcoord t i z]
  exact ClosedSmoothRiemannianMetric.hasDerivAt_coordinateGramVolumeDensityAt hgt

/-- A finite chart-density decomposition identifies the actual Hausdorff total
volume with a finite sum of scaled coordinate Lebesgue integrals. -/
theorem totalVolume_eq_sum_integral_of_finiteChartDensityDecomposition
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t : ℝ} (ht : t ∈ s) :
    totalVolume (gt t) =
      ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * D.density t i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
  let μ := volumeMeasure (gt t)
  letI : IsFiniteMeasure μ := volumeMeasure_isFiniteMeasure (gt t)
  have hpartition : μ Set.univ = ∑ i : Fin D.chartCount, μ (D.manifoldPiece i) := by
    have hdisj :
        (Set.univ : Set (Fin D.chartCount)).PairwiseDisjoint D.manifoldPiece :=
      D.pieces_pairwise
    have hsum := measure_biUnion_finset
      (μ := μ) (s := Finset.univ)
      (by simpa using hdisj)
      (fun i _hi => D.manifoldPiece_measurable i)
    calc
      μ Set.univ = μ (⋃ i, D.manifoldPiece i) := by rw [D.pieces_cover]
      _ = ∑ i : Fin D.chartCount, μ (D.manifoldPiece i) := by simpa using hsum
  have hpiece : ∀ i : Fin D.chartCount,
      μ (D.manifoldPiece i) =
        ENNReal.ofReal
          (∫ z : D.coordinateDomain i,
            (rawHausdorffLebesgueScale n : ℝ) * D.density t i z
            ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) := by
    intro i
    have hchart := D.chartMeasure t ht i
    have hmass :
        rawHausdorffCoordinateDensityMeasure
            (D.coordinateDomain i) (D.density t i) Set.univ =
          μ (D.manifoldPiece i) := by
      calc
        rawHausdorffCoordinateDensityMeasure
            (D.coordinateDomain i) (D.density t i) Set.univ =
            Measure.map (D.inverseChart i)
              (rawHausdorffCoordinateDensityMeasure
                (D.coordinateDomain i) (D.density t i)) Set.univ := by
              rw [Measure.map_apply (D.inverseChart_measurable i) MeasurableSet.univ]
              simp
        _ = (volumeMeasure (gt t)).restrict (D.manifoldPiece i) Set.univ := by
              rw [hchart]
        _ = μ (D.manifoldPiece i) := by
              simp [μ]
    rw [← hmass]
    exact rawHausdorffCoordinateDensityMeasure_univ_eq_ofReal_integral
      (D.density_integrable t ht i) (D.density_nonneg t ht i)
  rw [totalVolume, show volumeMeasure (gt t) = μ from rfl, hpartition]
  rw [ENNReal.toReal_sum (fun i _hi => measure_ne_top μ (D.manifoldPiece i))]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hpiece i]
  apply ENNReal.toReal_ofReal
  exact integral_nonneg_of_ae
    ((D.density_nonneg t ht i).mono fun z hz => mul_nonneg (by positivity) hz)

/-- Uniform dominated-differentiation data for the coordinate densities near
one time.  The hypotheses are exactly those consumed by Mathlib's parametric
integral theorem. -/
structure FiniteChartDensityDominatedDifferentiationAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s) (t₀ : ℝ) where
  timeSet_mem : s ∈ 𝓝 t₀
  densityDerivative :
    ℝ → (i : Fin D.chartCount) → D.coordinateDomain i → ℝ
  densityDerivative_aestronglyMeasurable_at : ∀ i,
    AEStronglyMeasurable (densityDerivative t₀ i)
      (coordinateLebesgueMeasure (D.coordinateDomain i))
  dominatingFunction : (i : Fin D.chartCount) → D.coordinateDomain i → ℝ
  dominatingFunction_integrable : ∀ i,
    Integrable (dominatingFunction i)
      (coordinateLebesgueMeasure (D.coordinateDomain i))
  densityDerivative_bound : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
      ∀ t ∈ s, ‖densityDerivative t i z‖ ≤ dominatingFunction i z
  hasDerivAt_density : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
      ∀ t ∈ s,
        HasDerivAt (fun τ => D.density τ i z) (densityDerivative t i z) t

/-- Dominated differentiation under one chart's coordinate-density integral. -/
theorem hasDerivAt_chartDensityIntegral_of_dominated
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (i : Fin D.chartCount) :
    HasDerivAt
      (fun t => ∫ z : D.coordinateDomain i,
        (rawHausdorffLebesgueScale n : ℝ) * D.density t i z
        ∂(coordinateLebesgueMeasure (D.coordinateDomain i)))
      (∫ z : D.coordinateDomain i,
        (rawHausdorffLebesgueScale n : ℝ) * A.densityDerivative t₀ i z
        ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) t₀ := by
  let μi := coordinateLebesgueMeasure (D.coordinateDomain i)
  let c : ℝ := rawHausdorffLebesgueScale n
  have hc : 0 ≤ c := by positivity
  have hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun z : D.coordinateDomain i =>
        c * D.density t i z) μi :=
    Filter.Eventually.mono A.timeSet_mem fun t ht =>
      ((D.density_integrable t ht i).const_mul c).aestronglyMeasurable
  have hF_int : Integrable
      (fun z : D.coordinateDomain i => c * D.density t₀ i z) μi :=
    (D.density_integrable t₀ (mem_of_mem_nhds A.timeSet_mem) i).const_mul c
  have hF'_meas : AEStronglyMeasurable
      (fun z : D.coordinateDomain i => c * A.densityDerivative t₀ i z) μi :=
    (A.densityDerivative_aestronglyMeasurable_at i).const_mul c
  have hbound :
      ∀ᵐ z ∂μi, ∀ t ∈ s,
        ‖c * A.densityDerivative t i z‖ ≤ c * A.dominatingFunction i z := by
    filter_upwards [A.densityDerivative_bound i] with z hz
    intro t ht
    calc
      ‖c * A.densityDerivative t i z‖ = c * ‖A.densityDerivative t i z‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hc]
      _ ≤ c * A.dominatingFunction i z := mul_le_mul_of_nonneg_left (hz t ht) hc
  have hbound_int : Integrable
      (fun z : D.coordinateDomain i => c * A.dominatingFunction i z) μi :=
    (A.dominatingFunction_integrable i).const_mul c
  have hdiff :
      ∀ᵐ z ∂μi, ∀ t ∈ s,
        HasDerivAt
          (fun τ => c * D.density τ i z)
          (c * A.densityDerivative t i z) t := by
    filter_upwards [A.hasDerivAt_density i] with z hz
    intro t ht
    exact (hz t ht).const_mul c
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μi)
    (F := fun t z => c * D.density t i z)
    (F' := fun t z => c * A.densityDerivative t i z)
    (bound := fun z => c * A.dominatingFunction i z)
    A.timeSet_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff).2

/-- The minimal local chart-measure equality, a finite measurable partition,
and standard dominated-differentiation data yield differentiation of the
actual Hausdorff-defined total volume. -/
theorem hasDerivAt_totalVolume_of_finiteChartDensityDecomposition
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀) :
    HasDerivAt (fun t => totalVolume (gt t))
      (∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * A.densityDerivative t₀ i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) t₀ := by
  have hsum : HasDerivAt
      (fun t => ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * D.density t i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)))
      (∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * A.densityDerivative t₀ i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) t₀ := by
    apply HasDerivAt.fun_sum
    intro i _hi
    exact hasDerivAt_chartDensityIntegral_of_dominated D A i
  apply hsum.congr_of_eventuallyEq
  exact Filter.Eventually.mono A.timeSet_mem fun t ht =>
    totalVolume_eq_sum_integral_of_finiteChartDensityDecomposition D ht

end Poincare
