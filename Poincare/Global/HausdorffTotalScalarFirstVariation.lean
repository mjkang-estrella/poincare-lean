import Poincare.Global.NormalizedFlowHausdorffDissipationEndpoint
import Poincare.Global.NormalizedFlowStokesBoundaryReduction
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Hausdorff chart-density first variation of total scalar curvature

The finite-chart Hausdorff package already differentiates total volume.  This
file applies the same mechanism to the moving integrand

`sqrt(det G(t)) * scalarAt(g(t))`.

A product rule gives the coordinate derivative, dominated parametric
integration differentiates each chart integral, and the proved local
Hausdorff change-of-variables theorem identifies the resulting finite sum with
`rawTotalScalarFirstVariation`.  The existing closed-Laplacian Stokes reduction
then changes that raw derivative into `normalizedMeanScalarEnergyNumerator`.

The global endpoint packages this data at every time and feeds it into the
absolute-dissipation Hamilton theorem.  Thus no independent moving-total-
scalar derivative hypothesis remains there.
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

/-- The scaled coordinate representative of the moving total-scalar
integrand. -/
noncomputable def coordinateScalarDensityAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (t : ℝ) (i : Fin D.chartCount) (z : D.coordinateDomain i) : ℝ :=
  (rawHausdorffLebesgueScale n : ℝ) *
    (D.density t i z * (gt t).scalarAt (D.inverseChart i z))

/-- Product-rule derivative of the coordinate total-scalar integrand.  The
density derivative is supplied by the volume package; the scalar derivative
is the actual one-variable derivative at the chart point. -/
noncomputable def coordinateScalarDensityVariationAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t₀ : ℝ} (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (t : ℝ) (i : Fin D.chartCount) (z : D.coordinateDomain i) : ℝ :=
  (rawHausdorffLebesgueScale n : ℝ) *
    (A.densityDerivative t i z *
        (gt t).scalarAt (D.inverseChart i z) +
      D.density t i z *
        deriv (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z)) t)

/-- Dominated-differentiation data for the product of chart density and
scalar curvature.

The assumptions are the exact inputs of Mathlib's local dominated parametric
integral theorem.  Scalar differentiability is recorded separately so the
coordinate product rule is proved rather than postulated.  The final field is
the global integrability needed by the Hausdorff change-of-variables theorem
when identifying the derivative with `rawTotalScalarFirstVariation`. -/
structure FiniteChartScalarDensityDominatedDifferentiationAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t₀ : ℝ} (A : FiniteChartDensityDominatedDifferentiationAt D t₀) where
  scalarDensity_integrable : ∀ t ∈ s, ∀ i,
    Integrable (coordinateScalarDensityAt D t i)
      (coordinateLebesgueMeasure (D.coordinateDomain i))
  scalarDensityVariation_aestronglyMeasurable_at : ∀ i,
    AEStronglyMeasurable (coordinateScalarDensityVariationAt D A t₀ i)
      (coordinateLebesgueMeasure (D.coordinateDomain i))
  dominatingFunction :
    (i : Fin D.chartCount) → D.coordinateDomain i → ℝ
  dominatingFunction_integrable : ∀ i,
    Integrable (dominatingFunction i)
      (coordinateLebesgueMeasure (D.coordinateDomain i))
  scalarDensityVariation_bound : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
      ∀ t ∈ s,
        ‖coordinateScalarDensityVariationAt D A t i z‖ ≤
          dominatingFunction i z
  hasDerivAt_scalar : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
      ∀ t ∈ s,
        HasDerivAt
          (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z))
          (deriv (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z)) t) t
  rawIntegrand_integrable : Integrable
    (fun x : M ↦
      deriv (fun τ ↦ (gt τ).scalarAt x) t₀ +
        (1 / 2 : ℝ) * (gt t₀).scalarAt x *
          traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x)
    (volumeMeasure (gt t₀))

omit [SecondCountableTopology M] in
/-- The coordinate total-scalar product has the stated derivative wherever
the density and scalar factors have their recorded derivatives. -/
theorem hasDerivAt_coordinateScalarDensityAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t₀ : ℝ} (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (i : Fin D.chartCount) (z : D.coordinateDomain i) {t : ℝ}
    (hDensity : HasDerivAt (fun τ ↦ D.density τ i z)
      (A.densityDerivative t i z) t)
    (hScalar : HasDerivAt
      (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z))
      (deriv (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z)) t) t) :
    HasDerivAt (fun τ ↦ coordinateScalarDensityAt D τ i z)
      (coordinateScalarDensityVariationAt D A t i z) t := by
  have hProduct := hDensity.mul hScalar
  have hScaled := hProduct.const_mul (rawHausdorffLebesgueScale n : ℝ)
  simpa [coordinateScalarDensityAt, coordinateScalarDensityVariationAt] using hScaled

omit [SecondCountableTopology M] in
/-- Dominated differentiation under one chart integral of
`density * scalarAt`. -/
theorem hasDerivAt_chartScalarDensityIntegral_of_dominated
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarDensityDominatedDifferentiationAt D A)
    (i : Fin D.chartCount) :
    HasDerivAt
      (fun t ↦ ∫ z : D.coordinateDomain i,
        coordinateScalarDensityAt D t i z
        ∂(coordinateLebesgueMeasure (D.coordinateDomain i)))
      (∫ z : D.coordinateDomain i,
        coordinateScalarDensityVariationAt D A t₀ i z
        ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) t₀ := by
  let μi := coordinateLebesgueMeasure (D.coordinateDomain i)
  have hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (coordinateScalarDensityAt D t i) μi :=
    Eventually.mono A.timeSet_mem fun t ht ↦
      (B.scalarDensity_integrable t ht i).aestronglyMeasurable
  have hF_int : Integrable (coordinateScalarDensityAt D t₀ i) μi :=
    B.scalarDensity_integrable t₀ (mem_of_mem_nhds A.timeSet_mem) i
  have hF'_meas :
      AEStronglyMeasurable (coordinateScalarDensityVariationAt D A t₀ i) μi :=
    B.scalarDensityVariation_aestronglyMeasurable_at i
  have hdiff :
      ∀ᵐ z ∂μi, ∀ t ∈ s,
        HasDerivAt (fun τ ↦ coordinateScalarDensityAt D τ i z)
          (coordinateScalarDensityVariationAt D A t i z) t := by
    filter_upwards [A.hasDerivAt_density i, B.hasDerivAt_scalar i] with z hD hR
    intro t ht
    exact hasDerivAt_coordinateScalarDensityAt D A i z
      (hD t ht) (hR t ht)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μi)
    (F := fun t z ↦ coordinateScalarDensityAt D t i z)
    (F' := fun t z ↦ coordinateScalarDensityVariationAt D A t i z)
    (bound := B.dominatingFunction i)
    A.timeSet_mem hF_meas hF_int hF'_meas
      (B.scalarDensityVariation_bound i)
      (B.dominatingFunction_integrable i) hdiff).2

omit [SecondCountableTopology M] in
/-- A finite chart-density decomposition expresses actual total scalar
curvature as the sum of its coordinate density integrals. -/
theorem totalScalar_eq_sum_coordinateScalarDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t : ℝ} (ht : t ∈ s) :
    totalScalar (gt t) =
      ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          coordinateScalarDensityAt D t i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
  have hCoordinate := integral_eq_sum_rawHausdorff_coordinateDensity
    D ht (fun x : M ↦ (gt t).scalarAt x) (scalarAt_integrable (gt t))
  change (∫ x, (gt t).scalarAt x ∂(volumeMeasure (gt t))) = _
  rw [hCoordinate]
  apply Finset.sum_congr rfl
  intro i _hi
  apply integral_congr_ae
  exact Eventually.of_forall fun z ↦ by
    simp only [coordinateScalarDensityAt]
    ring

omit [SecondCountableTopology M] in
/-- The finite sum of coordinate product derivatives is exactly the raw
moving-total-scalar first variation. -/
theorem rawTotalScalarFirstVariation_eq_sum_coordinateScalarDensityVariation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarDensityDominatedDifferentiationAt D A)
    (hcoord : D.UsesCoordinateGramDensity)
    (hTimeDifferentiable : ∀ i : Fin D.chartCount,
      ∀ z : D.coordinateDomain i,
        TimeDifferentiableAt gt t₀ (D.inverseChart i z)) :
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
    exact (hz t₀ ht₀).unique
      (D.hasDerivAt_density_of_coordinateGram hcoord i z
        (hTimeDifferentiable i z))
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
/-- Finite dominated chart differentiation proves the derivative of the
actual Hausdorff-defined total scalar curvature and identifies it with the raw
first-variation functional. -/
theorem hasDerivAt_totalScalar_rawFirstVariation_of_finiteChartDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarDensityDominatedDifferentiationAt D A)
    (hcoord : D.UsesCoordinateGramDensity)
    (hTimeDifferentiable : ∀ i : Fin D.chartCount,
      ∀ z : D.coordinateDomain i,
        TimeDifferentiableAt gt t₀ (D.inverseChart i z)) :
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
  have hRaw := rawTotalScalarFirstVariation_eq_sum_coordinateScalarDensityVariation
    D A B hcoord hTimeDifferentiable
  rw [← hRaw] at hsum
  apply hsum.congr_of_eventuallyEq
  exact Eventually.mono A.timeSet_mem fun t ht ↦
    totalScalar_eq_sum_coordinateScalarDensity D ht

omit [SecondCountableTopology M] in
/-- Closed-Laplacian Stokes changes the chart-proved raw derivative into the
normalized mean-scalar energy numerator. -/
theorem hasDerivAt_totalScalar_energyNumerator_of_finiteChartDensity
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarDensityDominatedDifferentiationAt D A)
    (hcoord : D.UsesCoordinateGramDensity)
    (hTimeDifferentiable : ∀ i : Fin D.chartCount,
      ∀ z : D.coordinateDomain i,
        TimeDifferentiableAt gt t₀ (D.inverseChart i z))
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y)
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
  exact hasDerivAt_totalScalar_rawFirstVariation_of_finiteChartDensity
    D A B hcoord hTimeDifferentiable

/-- Finite Hausdorff volume and total-scalar chart packages at every time. -/
structure GlobalFiniteHausdorffChartScalarVariation
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  volumeVariation : GlobalFiniteHausdorffChartDensityVariation gt
  scalarDifferentiation : ∀ t : ℝ,
    FiniteChartScalarDensityDominatedDifferentiationAt
      (volumeVariation.decomposition t) (volumeVariation.differentiation t)

omit [SecondCountableTopology M] in
/-- The global chart package supplies the actual raw moving-total-scalar
derivative at every time. -/
theorem GlobalFiniteHausdorffChartScalarVariation.hasDerivAt_totalScalar_raw
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteHausdorffChartScalarVariation gt) (t : ℝ) :
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (rawTotalScalarFirstVariation gt t) t :=
  hasDerivAt_totalScalar_rawFirstVariation_of_finiteChartDensity
    (H.volumeVariation.decomposition t)
    (H.volumeVariation.differentiation t)
    (H.scalarDifferentiation t)
    (H.volumeVariation.usesCoordinateGramDensity t)
    (H.volumeVariation.timeDifferentiable t)

omit [SecondCountableTopology M] in
/-- Under normalized flow and closed-Laplacian Stokes, the global chart
package supplies the energy-numerator derivative at every time. -/
theorem GlobalFiniteHausdorffChartScalarVariation.hasDerivAt_totalScalar_energyNumerator
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (H : GlobalFiniteHausdorffChartScalarVariation gt)
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
  apply hasDerivAt_totalScalar_energyNumerator_of_finiteChartDensity
    (H.volumeVariation.decomposition t)
    (H.volumeVariation.differentiation t)
    (H.scalarDifferentiation t)
    (H.volumeVariation.usesCoordinateGramDensity t)
    (H.volumeVariation.timeDifferentiable t)
    (hFlow t) hn (hScalar₂ t) (hScalarVariation t) (hStokes t)

section DimensionThreeEndpoint

variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The all-time Hausdorff volume/scalar chart package removes both moving
Hausdorff-integral derivative hypotheses from the absolute-dissipation
Hamilton endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartScalarVariation_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (H : GlobalFiniteHausdorffChartScalarVariation gt)
    (hScalar₂ : ∀ t : ℝ, ∀ y : M,
      ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
        (fun z : M ↦ (gt t).scalarAt z) y)
    (hScalarVariation : ∀ t : ℝ, ∀ x : M,
      deriv (fun s ↦ (gt s).scalarAt x) t =
        scalarVariationStokesBoundaryAt gt t x -
          metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartDensity_of_scalarLower
      gt hFlow
      (fun t ↦ H.hasDerivAt_totalScalar_energyNumerator
        hFlow (by norm_num) hScalar₂ hScalarVariation hStokes t)
      H.volumeVariation hFiniteDissipation hCompact hc hScalarLower

end DimensionThreeEndpoint

end Poincare
