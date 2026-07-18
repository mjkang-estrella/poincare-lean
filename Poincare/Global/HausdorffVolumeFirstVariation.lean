import Poincare.Global.HausdorffCoordinateDensityVariation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Coordinate-density identification of the intrinsic volume variation

This file continues the finite-chart Hausdorff-density reduction.  It proves
the change-of-variables formula for ordinary real integrals from the local
measure equality, then identifies the finite sum of coordinate density
derivatives with `totalVolumeFirstVariation`.
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

/-- The local Hausdorff chart-density equality transports an integrable real
function to the expected scaled coordinate-density integral. -/
theorem integral_restrict_eq_rawHausdorff_coordinateDensity
    (g : ClosedSmoothRiemannianMetric n M)
    {U : Set (ClosedSmoothModel n)} {ψ : U → M} {V : Set M}
    {δ : U → ℝ}
    (hψ : Measurable ψ)
    (hchart : HausdorffChartDensityEquality g U ψ V δ)
    (hδ : Integrable δ (coordinateLebesgueMeasure U))
    (hδnonneg : 0 ≤ᵐ[coordinateLebesgueMeasure U] δ)
    (f : M → ℝ)
    (hf : Integrable f ((volumeMeasure g).restrict V)) :
    (∫ x, f x ∂((volumeMeasure g).restrict V)) =
      ∫ z : U,
        (rawHausdorffLebesgueScale n : ℝ) * δ z * f (ψ z)
        ∂(coordinateLebesgueMeasure U) := by
  let μU := coordinateLebesgueMeasure U
  let c : ℝ := rawHausdorffLebesgueScale n
  let w : U → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (c * δ z)
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hwMeas : AEMeasurable w μU := by
    exact ((hδ.aestronglyMeasurable.const_mul c).aemeasurable).ennreal_ofReal
  have hwTop : ∀ᵐ z ∂μU, w z < (⊤ : ℝ≥0∞) :=
    Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top
  have hfMap : AEStronglyMeasurable f
      (Measure.map ψ (rawHausdorffCoordinateDensityMeasure U δ)) := by
    rw [hchart]
    exact hf.aestronglyMeasurable
  calc
    (∫ x, f x ∂((volumeMeasure g).restrict V)) =
        ∫ x, f x
          ∂(Measure.map ψ (rawHausdorffCoordinateDensityMeasure U δ)) := by
            rw [hchart]
    _ = ∫ z : U, f (ψ z)
          ∂(rawHausdorffCoordinateDensityMeasure U δ) :=
        MeasureTheory.integral_map hψ.aemeasurable hfMap
    _ = ∫ z : U, (w z).toReal • f (ψ z) ∂μU := by
        exact integral_withDensity_eq_integral_toReal_smul₀
          hwMeas hwTop (fun z : U ↦ f (ψ z))
    _ = ∫ z : U, c * δ z * f (ψ z) ∂μU := by
        apply integral_congr_ae
        filter_upwards [hδnonneg] with z hz
        have hwReal : (w z).toReal = c * δ z := by
          dsimp only [w]
          exact ENNReal.toReal_ofReal (mul_nonneg hc hz)
        rw [hwReal]
        simp only [smul_eq_mul]

/-- A finite Hausdorff chart-density decomposition transports a global
integral to the finite sum of its coordinate-density integrals. -/
theorem integral_eq_sum_rawHausdorff_coordinateDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t : ℝ} (ht : t ∈ s) (f : M → ℝ)
    (hf : Integrable f (volumeMeasure (gt t))) :
    (∫ x, f x ∂(volumeMeasure (gt t))) =
      ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * D.density t i z *
            f (D.inverseChart i z)
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
  let μ := volumeMeasure (gt t)
  have hpairwise : Pairwise (fun i j ↦
      Disjoint (D.manifoldPiece i) (D.manifoldPiece j)) := by
    intro i j hij
    exact D.pieces_pairwise (mem_univ i) (mem_univ j) hij
  have hsplit :
      (∫ x, f x ∂μ) =
        ∑ i : Fin D.chartCount,
          ∫ x in D.manifoldPiece i, f x ∂μ := by
    calc
      (∫ x, f x ∂μ) = ∫ x in ⋃ i, D.manifoldPiece i, f x ∂μ := by
        rw [D.pieces_cover, setIntegral_univ]
      _ = _ := integral_iUnion_fintype D.manifoldPiece_measurable
        hpairwise (fun i ↦ hf.integrableOn)
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro i _hi
  exact integral_restrict_eq_rawHausdorff_coordinateDensity
    (gt t) (D.inverseChart_measurable i) (D.chartMeasure t ht i)
      (D.density_integrable t ht i) (D.density_nonneg t ht i) f
      (hf.mono_measure Measure.restrict_le_self)

/-- The intrinsic first-variation functional is exactly the finite sum of
one-half Gram-density times the pulled-back metric-speed trace. -/
theorem totalVolumeFirstVariation_eq_sum_coordinateDensityDerivative
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t : ℝ} (ht : t ∈ s)
    (hTraceIntegrable : Integrable
      (fun x : M ↦ traceMetricVariationAt (gt t) (timeDerivAt gt t) x)
      (volumeMeasure (gt t))) :
    totalVolumeFirstVariation (gt t) (timeDerivAt gt t) =
      ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) *
            ((1 / 2 : ℝ) * D.density t i z *
              traceMetricVariationAt (gt t) (timeDerivAt gt t)
                (D.inverseChart i z))
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
  rw [totalVolumeFirstVariation]
  rw [integral_eq_sum_rawHausdorff_coordinateDensity D ht _
    hTraceIntegrable]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z ↦ by ring

/-- With the proved Gram-density derivative, the local Hausdorff chart
equality and standard dominated convergence identify the derivative of the
actual Hausdorff-defined total volume with the intrinsic first variation. -/
theorem hasDerivAt_totalVolume_firstVariation_of_finiteChartDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (hcoord : D.UsesCoordinateGramDensity)
    (hTimeDifferentiable : ∀ i : Fin D.chartCount,
      ∀ z : D.coordinateDomain i,
        TimeDifferentiableAt gt t₀ (D.inverseChart i z))
    (hTraceIntegrable : Integrable
      (fun x : M ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x)
      (volumeMeasure (gt t₀))) :
    HasDerivAt (fun t ↦ totalVolume (gt t))
      (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀ := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds A.timeSet_mem
  have hDerivativeAE : ∀ i : Fin D.chartCount,
      ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
        A.densityDerivative t₀ i z =
          (1 / 2 : ℝ) * D.density t₀ i z *
            traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
              (D.inverseChart i z) := by
    intro i
    filter_upwards [A.hasDerivAt_density i] with z hz
    exact (hz t₀ ht₀).unique
      (D.hasDerivAt_density_of_coordinateGram hcoord i z
        (hTimeDifferentiable i z))
  have hDerivativeSum :
      (∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) *
            A.densityDerivative t₀ i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) =
        ∑ i : Fin D.chartCount,
          ∫ z : D.coordinateDomain i,
            (rawHausdorffLebesgueScale n : ℝ) *
              ((1 / 2 : ℝ) * D.density t₀ i z *
                traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
                  (D.inverseChart i z))
            ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply integral_congr_ae
    filter_upwards [hDerivativeAE i] with z hz
    rw [hz]
  have hIntrinsic :=
    totalVolumeFirstVariation_eq_sum_coordinateDensityDerivative
      D ht₀ hTraceIntegrable
  have hbase :=
    hasDerivAt_totalVolume_of_finiteChartDensityDecomposition D A
  rw [hDerivativeSum, ← hIntrinsic] at hbase
  exact hbase

/-- For a normalized Ricci flow, the finite-chart Hausdorff-density package
therefore proves that the actual total-volume derivative is zero. -/
theorem hasDerivAt_totalVolume_zero_of_finiteChartDensity_normalizedRicciFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (hcoord : D.UsesCoordinateGramDensity)
    (hTimeDifferentiable : ∀ i : Fin D.chartCount,
      ∀ z : D.coordinateDomain i,
        TimeDifferentiableAt gt t₀ (D.inverseChart i z))
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    HasDerivAt (fun t ↦ totalVolume (gt t)) 0 t₀ := by
  apply hasDerivAt_totalVolume_zero_of_closedNormalizedRicciFlow hFlow hn
  exact hasDerivAt_totalVolume_firstVariation_of_finiteChartDensity
    D A hcoord hTimeDifferentiable
      (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
        hFlow hn)

/-- Finite Hausdorff chart-density and dominated-differentiation data at every
time of a metric family.  This is the global form of the sole local
area-formula boundary isolated in `HausdorffChartDensityEquality`. -/
structure GlobalFiniteHausdorffChartDensityVariation
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  timeSet : ℝ → Set ℝ
  decomposition : ∀ t : ℝ,
    FiniteHausdorffChartDensityDecomposition gt (timeSet t)
  differentiation : ∀ t : ℝ,
    FiniteChartDensityDominatedDifferentiationAt (decomposition t) t
  usesCoordinateGramDensity : ∀ t : ℝ,
    (decomposition t).UsesCoordinateGramDensity
  timeDifferentiable : ∀ t : ℝ,
    ∀ i : Fin (decomposition t).chartCount,
      ∀ z : (decomposition t).coordinateDomain i,
        TimeDifferentiableAt gt t ((decomposition t).inverseChart i z)

/-- Global finite Hausdorff chart-density variation supplies the previously
abstract total-volume first-variation identification at every time. -/
theorem GlobalFiniteHausdorffChartDensityVariation.hasDerivAt_totalVolume
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteHausdorffChartDensityVariation gt) (t : ℝ)
    (hTraceIntegrable : Integrable
      (fun x : M ↦ traceMetricVariationAt (gt t) (timeDerivAt gt t) x)
      (volumeMeasure (gt t))) :
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t :=
  hasDerivAt_totalVolume_firstVariation_of_finiteChartDensity
    (H.decomposition t) (H.differentiation t)
      (H.usesCoordinateGramDensity t) (H.timeDifferentiable t)
        hTraceIntegrable

/-- Consequently, a normalized closed Ricci flow carrying this explicit
global chart-density package has genuinely constant Hausdorff total volume. -/
theorem totalVolume_eq_of_closedNormalizedRicciFlow_of_globalFiniteChartDensity
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hn : (n : ℝ) ≠ 0)
    (H : GlobalFiniteHausdorffChartDensityVariation gt)
    (s t : ℝ) :
    totalVolume (gt s) = totalVolume (gt t) := by
  apply totalVolume_eq_of_closedNormalizedRicciFlow hFlow hn
  intro r
  exact H.hasDerivAt_totalVolume r
    (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
      (hFlow r) hn)

end Poincare
