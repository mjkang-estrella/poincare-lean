import Poincare.Global.NormalizedFlowScalarRegularity

/-!
# Hausdorff scalar-density domination without derivative witnesses

`FiniteChartScalarDensityDominatedDifferentiationAt` originally bundled two
facts that are now consequences of stronger geometric packages:

* pointwise scalar differentiability follows from the automatic
  Lichnerowicz/`δΓ` assemblies;
* integrability of the raw moving-total-scalar density follows, under
  normalized flow, from the closed first-variation integrability theorem and
  `ClosedLaplacianStokes`.

This file isolates the genuinely analytic input that remains: integrability of
the coordinate scalar density, measurability of its variation, and an
integrable dominating bound.  It reconstructs the old full package and feeds
the strongest Hausdorff/Lichnerowicz/lower-semicontinuous endpoint.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section LocalDomination

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- The analytic part of dominated differentiation for the moving coordinate
integrand `density * scalarAt`.  Scalar differentiability and global raw
integrability are intentionally not fields. -/
structure FiniteChartScalarDensityDominationAt
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

/-- Add actual scalar differentiation and global raw-integrand integrability
to the analytic domination data, reconstructing the full package consumed by
the Hausdorff total-scalar theorem. -/
def FiniteChartScalarDensityDominationAt.toDominatedDifferentiation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s}
    {t₀ : ℝ} {A : FiniteChartDensityDominatedDifferentiationAt D t₀}
    (B : FiniteChartScalarDensityDominationAt D A)
    (hScalar : ∀ i : Fin D.chartCount,
      ∀ z : D.coordinateDomain i, ∀ t ∈ s,
        HasDerivAt
          (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z))
          (deriv (fun τ ↦ (gt τ).scalarAt (D.inverseChart i z)) t) t)
    (hRaw : Integrable
      (fun x : M ↦
        deriv (fun τ ↦ (gt τ).scalarAt x) t₀ +
          (1 / 2 : ℝ) * (gt t₀).scalarAt x *
            traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x)
      (volumeMeasure (gt t₀))) :
    FiniteChartScalarDensityDominatedDifferentiationAt D A where
  scalarDensity_integrable := B.scalarDensity_integrable
  scalarDensityVariation_aestronglyMeasurable_at :=
    B.scalarDensityVariation_aestronglyMeasurable_at
  dominatingFunction := B.dominatingFunction
  dominatingFunction_integrable := B.dominatingFunction_integrable
  scalarDensityVariation_bound := B.scalarDensityVariation_bound
  hasDerivAt_scalar := fun i ↦ Eventually.of_forall fun z t ht ↦
    hScalar i z t ht
  rawIntegrand_integrable := hRaw

end LocalDomination

section GlobalDomination

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n

/-- Scalar-density domination at every time, relative to an already explicit
Hausdorff volume-density package. -/
structure GlobalFiniteHausdorffChartScalarDomination
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (V : GlobalFiniteHausdorffChartDensityVariation gt) where
  scalarDomination : ∀ t : ℝ,
    FiniteChartScalarDensityDominationAt
      (V.decomposition t) (V.differentiation t)

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M] in
/-- Automatic Lichnerowicz assemblies provide the actual scalar
`HasDerivAt` field expected by each local Hausdorff domination package. -/
theorem GlobalLichnerowiczAssemblyRegularity.hasDerivAt_scalar_deriv
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (L : GlobalLichnerowiczAssemblyRegularity gt) (t : ℝ) (x : M) :
    HasDerivAt (fun s ↦ (gt s).scalarAt x)
      (deriv (fun s ↦ (gt s).scalarAt x) t) t := by
  have h := L.hasDerivAt_scalar_stokes t x
  rw [h.deriv]
  exact h

omit [SecondCountableTopology M] in
/-- Under normalized flow, the raw moving-total-scalar integrand is
integrable from the automatic scalar variation, the closed non-boundary first
variation, and the sole primary Stokes statement. -/
theorem rawTotalScalarFirstVariation_integrand_integrable_of_normalizedFlow_of_lichnerowicz_of_stokes
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hn : (n : ℝ) ≠ 0)
    (L : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (t : ℝ) :
    Integrable
      (fun x : M ↦
        deriv (fun s ↦ (gt s).scalarAt x) t +
          (1 / 2 : ℝ) * (gt t).scalarAt x *
            traceMetricVariationAt (gt t) (timeDerivAt gt t) x)
      (volumeMeasure (gt t)) := by
  have hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t).scalarAt z) y :=
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      (hFlow t) (L.timeVariationEntries t)
  have hClosed :=
    closedTotalScalarFirstVariation_integrand_integrable (hFlow t) hn
  have hSum := (hStokes t).1.add hClosed
  apply hSum.congr
  exact Eventually.of_forall fun x ↦ by
    change
      (gt t).laplacianAt (fun y ↦ (gt t).scalarAt y) x +
          ((1 / 2 : ℝ) * (gt t).scalarAt x *
              traceMetricVariationAt (gt t) (timeDerivAt gt t) x -
            metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x) =
        deriv (fun s ↦ (gt s).scalarAt x) t +
          (1 / 2 : ℝ) * (gt t).scalarAt x *
            traceMetricVariationAt (gt t) (timeDerivAt gt t) x
    rw [L.scalarVariation_stokes t x,
      scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt_of_normalizedFlow
        (hFlow t) hn hScalar₂]
    ring

/-- Reconstruct the former global Hausdorff scalar-variation package from
pure scalar-density domination plus automatic geometric differentiation. -/
def GlobalFiniteHausdorffChartScalarDomination.toScalarVariation
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    {V : GlobalFiniteHausdorffChartDensityVariation gt}
    (B : GlobalFiniteHausdorffChartScalarDomination V)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hn : (n : ℝ) ≠ 0)
    (L : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y)) :
    GlobalFiniteHausdorffChartScalarVariation gt where
  volumeVariation := V
  scalarDifferentiation t :=
    (B.scalarDomination t).toDominatedDifferentiation
      (fun _i _z s _hs ↦ L.hasDerivAt_scalar_deriv s _)
      (rawTotalScalarFirstVariation_integrand_integrable_of_normalizedFlow_of_lichnerowicz_of_stokes
        hFlow hn L hStokes t)

end GlobalDomination

section DimensionThreeEndpoint

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The scalar Hausdorff input at the strongest LSC endpoint now contains
only analytic domination; all derivative and raw-integrability witnesses are
constructed from normalized flow, Lichnerowicz regularity, and Stokes. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffScalarDomination_of_globalLichnerowiczRegularity_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartScalarDomination hHausdorffVolume)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_lscCompactness
      hFlow
      (hScalarDomination.toScalarVariation
        hFlow (by norm_num) hLichnerowicz hStokes)
      hLichnerowicz hStokes hFiniteDissipation hCompact hc hScalarLower

end DimensionThreeEndpoint

end Poincare
