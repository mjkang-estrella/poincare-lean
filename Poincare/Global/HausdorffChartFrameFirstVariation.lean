import Poincare.Global.HausdorffTotalScalarFirstVariation

/-!
# Hausdorff first variations with an honest chart-frame density

The original finite-coordinate package identifies its density with
`coordinateGramVolumeDensityAt`, which is computed in Mathlib's selected
finite basis of each tangent fiber.  A coordinate change-of-variables formula
instead uses the Gram determinant in the derivative frame of the inverse
chart.  Those numerical densities need not agree.

Only their intrinsic time derivative is used by the volume and total-scalar
arguments.  This file records precisely that derivative, proves both first
variations from it, and packages an all-time route which no longer assumes an
equality between unrelated frames.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n

/-- The chart density has the intrinsic Riemannian first variation at one
time.  Unlike `UsesCoordinateGramDensity`, this does not identify the density
itself with the determinant in an unrelated selected tangent basis. -/
def FiniteHausdorffChartDensityDecomposition.HasIntrinsicDensityFirstVariationAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s) (t₀ : ℝ) : Prop :=
  ∀ (i : Fin D.chartCount) (z : D.coordinateDomain i),
    HasDerivAt (fun t ↦ D.density t i z)
      ((1 / 2 : ℝ) * D.density t₀ i z *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
          (D.inverseChart i z)) t₀

omit [SecondCountableTopology M] in
/-- The older selected-basis equality implies the honest intrinsic derivative,
so existing providers can be embedded in the corrected interface. -/
theorem FiniteHausdorffChartDensityDecomposition.hasIntrinsicDensityFirstVariationAt_of_coordinateGram
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (hcoord : D.UsesCoordinateGramDensity) (t₀ : ℝ)
    (hTimeDifferentiable : ∀ i : Fin D.chartCount,
      ∀ z : D.coordinateDomain i,
        TimeDifferentiableAt gt t₀ (D.inverseChart i z)) :
    D.HasIntrinsicDensityFirstVariationAt t₀ := by
  intro i z
  exact D.hasDerivAt_density_of_coordinateGram hcoord i z
    (hTimeDifferentiable i z)

omit [SecondCountableTopology M] in
/-- Dominated differentiation plus the intrinsic chart-frame density
variation identifies the derivative of actual Hausdorff volume. -/
theorem hasDerivAt_totalVolume_firstVariation_of_intrinsicChartDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (hDensity : D.HasIntrinsicDensityFirstVariationAt t₀)
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
    exact (hz t₀ ht₀).unique (hDensity i z)
  have hDerivativeSum :
      (∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * A.densityDerivative t₀ i z
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

omit [SecondCountableTopology M] in
/-- The corrected chart-frame package still gives constant Hausdorff volume
for a closed normalized Ricci flow. -/
theorem hasDerivAt_totalVolume_zero_of_intrinsicChartDensity_normalizedRicciFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (hDensity : D.HasIntrinsicDensityFirstVariationAt t₀)
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    HasDerivAt (fun t ↦ totalVolume (gt t)) 0 t₀ := by
  apply hasDerivAt_totalVolume_zero_of_closedNormalizedRicciFlow hFlow hn
  exact hasDerivAt_totalVolume_firstVariation_of_intrinsicChartDensity
    D A hDensity
      (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
        hFlow hn)

/-- All-time Hausdorff chart-density data with the correct frame-independent
first-variation contract.  Pointwise metric differentiability remains visible
because the later Lichnerowicz regularity assembly also consumes it. -/
structure GlobalFiniteHausdorffChartFrameDensityVariation
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  timeSet : ℝ → Set ℝ
  decomposition : ∀ t : ℝ,
    FiniteHausdorffChartDensityDecomposition gt (timeSet t)
  differentiation : ∀ t : ℝ,
    FiniteChartDensityDominatedDifferentiationAt (decomposition t) t
  intrinsicDensityFirstVariation : ∀ t : ℝ,
    (decomposition t).HasIntrinsicDensityFirstVariationAt t
  timeDifferentiable : ∀ t : ℝ,
    ∀ i : Fin (decomposition t).chartCount,
      ∀ z : (decomposition t).coordinateDomain i,
        TimeDifferentiableAt gt t ((decomposition t).inverseChart i z)

/-- Every legacy selected-basis provider yields a corrected chart-frame
provider, but the converse is intentionally unnecessary. -/
def GlobalFiniteHausdorffChartDensityVariation.toChartFrameVariation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteHausdorffChartDensityVariation gt) :
    GlobalFiniteHausdorffChartFrameDensityVariation gt where
  timeSet := H.timeSet
  decomposition := H.decomposition
  differentiation := H.differentiation
  intrinsicDensityFirstVariation t :=
    (H.decomposition t).hasIntrinsicDensityFirstVariationAt_of_coordinateGram
      (H.usesCoordinateGramDensity t) t (H.timeDifferentiable t)
  timeDifferentiable := H.timeDifferentiable

omit [SecondCountableTopology M] in
/-- The corrected global package proves total-volume first variation. -/
theorem GlobalFiniteHausdorffChartFrameDensityVariation.hasDerivAt_totalVolume
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteHausdorffChartFrameDensityVariation gt) (t : ℝ)
    (hTraceIntegrable : Integrable
      (fun x : M ↦ traceMetricVariationAt (gt t) (timeDerivAt gt t) x)
      (volumeMeasure (gt t))) :
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t :=
  hasDerivAt_totalVolume_firstVariation_of_intrinsicChartDensity
    (H.decomposition t) (H.differentiation t)
      (H.intrinsicDensityFirstVariation t) hTraceIntegrable

omit [SecondCountableTopology M] in
/-- Closed normalized flow plus the corrected package has constant total
Hausdorff volume. -/
theorem totalVolume_eq_of_closedNormalizedRicciFlow_of_globalChartFrameDensity
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hn : (n : ℝ) ≠ 0)
    (H : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (s t : ℝ) :
    totalVolume (gt s) = totalVolume (gt t) := by
  apply totalVolume_eq_of_closedNormalizedRicciFlow hFlow hn
  intro r
  exact H.hasDerivAt_totalVolume r
    (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
      (hFlow r) hn)

omit [SecondCountableTopology M] in
/-- The raw total-scalar first variation only needs the intrinsic derivative
of the actual chart density. -/
theorem rawTotalScalarFirstVariation_eq_sum_coordinateScalarDensityVariation_of_intrinsicChartDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarDensityDominatedDifferentiationAt D A)
    (hDensity : D.HasIntrinsicDensityFirstVariationAt t₀) :
    rawTotalScalarFirstVariation gt t₀ =
      ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          coordinateScalarDensityVariationAt D A t₀ i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds A.timeSet_mem
  have hDensityDerivative : ∀ i : Fin D.chartCount,
      ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
        A.densityDerivative t₀ i z =
          (1 / 2 : ℝ) * D.density t₀ i z *
            traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
              (D.inverseChart i z) := by
    intro i
    filter_upwards [A.hasDerivAt_density i] with z hz
    exact (hz t₀ ht₀).unique (hDensity i z)
  have hRawCoordinate :
      rawTotalScalarFirstVariation gt t₀ =
        ∑ i : Fin D.chartCount,
          ∫ z : D.coordinateDomain i,
            (rawHausdorffLebesgueScale n : ℝ) * D.density t₀ i z *
              (deriv (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z)) t₀ +
                (1 / 2 : ℝ) *
                  (gt t₀).scalarAt (D.inverseChart i z) *
                  traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
                    (D.inverseChart i z))
            ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
    unfold rawTotalScalarFirstVariation
    exact integral_eq_sum_rawHausdorff_coordinateDensity D ht₀ _
      B.rawIntegrand_integrable
  rw [hRawCoordinate]
  apply Finset.sum_congr rfl
  intro i _hi
  apply integral_congr_ae
  filter_upwards [hDensityDerivative i] with z hz
  simp only [coordinateScalarDensityVariationAt, hz]
  ring

omit [SecondCountableTopology M] in
/-- Dominated coordinate differentiation therefore differentiates the actual
Hausdorff total scalar curvature without a selected-basis density equality. -/
theorem hasDerivAt_totalScalar_rawFirstVariation_of_intrinsicChartDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarDensityDominatedDifferentiationAt D A)
    (hDensity : D.HasIntrinsicDensityFirstVariationAt t₀) :
    HasDerivAt (fun t ↦ totalScalar (gt t))
      (rawTotalScalarFirstVariation gt t₀) t₀ := by
  have hsum : HasDerivAt
      (fun t ↦ ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          coordinateScalarDensityAt D t i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)))
      (∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          coordinateScalarDensityVariationAt D A t₀ i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) t₀ := by
    apply HasDerivAt.fun_sum
    intro i _hi
    exact hasDerivAt_chartScalarDensityIntegral_of_dominated D A B i
  have hRaw :=
    rawTotalScalarFirstVariation_eq_sum_coordinateScalarDensityVariation_of_intrinsicChartDensity
      D A B hDensity
  rw [← hRaw] at hsum
  apply hsum.congr_of_eventuallyEq
  exact Eventually.mono A.timeSet_mem fun t ht ↦
    totalScalar_eq_sum_coordinateScalarDensity D ht

omit [SecondCountableTopology M] in
/-- Stokes turns the corrected raw derivative into the normalized
mean-scalar energy numerator. -/
theorem hasDerivAt_totalScalar_energyNumerator_of_intrinsicChartDensity
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarDensityDominatedDifferentiationAt D A)
    (hDensity : D.HasIntrinsicDensityFirstVariationAt t₀)
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y)) :
    HasDerivAt (fun t ↦ totalScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀ := by
  apply
    hasDerivAt_totalScalar_energyNumerator_of_normalizedFlow_closedLaplacianStokes
      hFlow hn hScalar₂ hScalarVariation hStokes
  exact hasDerivAt_totalScalar_rawFirstVariation_of_intrinsicChartDensity
    D A B hDensity

/-- Corrected all-time Hausdorff volume and total-scalar chart data. -/
structure GlobalFiniteHausdorffChartFrameScalarVariation
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  volumeVariation : GlobalFiniteHausdorffChartFrameDensityVariation gt
  scalarDifferentiation : ∀ t : ℝ,
    FiniteChartScalarDensityDominatedDifferentiationAt
      (volumeVariation.decomposition t) (volumeVariation.differentiation t)

omit [SecondCountableTopology M] in
/-- The corrected global package supplies the actual raw total-scalar
derivative at every time. -/
theorem GlobalFiniteHausdorffChartFrameScalarVariation.hasDerivAt_totalScalar_raw
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteHausdorffChartFrameScalarVariation gt) (t : ℝ) :
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (rawTotalScalarFirstVariation gt t) t :=
  hasDerivAt_totalScalar_rawFirstVariation_of_intrinsicChartDensity
    (H.volumeVariation.decomposition t)
    (H.volumeVariation.differentiation t)
    (H.scalarDifferentiation t)
    (H.volumeVariation.intrinsicDensityFirstVariation t)

omit [SecondCountableTopology M] in
/-- Under normalized flow and Stokes, the corrected global package supplies
the energy-numerator derivative at every time. -/
theorem GlobalFiniteHausdorffChartFrameScalarVariation.hasDerivAt_totalScalar_energyNumerator
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (H : GlobalFiniteHausdorffChartFrameScalarVariation gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ t : ℝ, ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t).scalarAt z) y)
    (hScalarVariation : ∀ t : ℝ, ∀ x : M,
      deriv (fun s ↦ (gt s).scalarAt x) t =
        scalarVariationStokesBoundaryAt gt t x -
          metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (t : ℝ) :
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t := by
  exact hasDerivAt_totalScalar_energyNumerator_of_intrinsicChartDensity
    (H.volumeVariation.decomposition t)
    (H.volumeVariation.differentiation t)
    (H.scalarDifferentiation t)
    (H.volumeVariation.intrinsicDensityFirstVariation t)
    (hFlow t) hn (hScalar₂ t) (hScalarVariation t) (hStokes t)

end Poincare
