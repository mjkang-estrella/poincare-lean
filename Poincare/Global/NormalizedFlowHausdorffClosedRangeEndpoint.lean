import Poincare.Global.NormalizedFlowMeanScalarLimit
import Poincare.Global.NormalizedFlowScalarRegularity
import Poincare.Global.NormalizedFlowAbsoluteDissipationDecay

/-!
# Hausdorff/Lichnerowicz Hamilton endpoint with scalar-invariant closure

This file combines the actual Hausdorff moving-integral construction and the
automatic Lichnerowicz assemblies with the finite-dimensional closed-range
endpoint.  Smooth metric subsequence extraction is no longer an input: the
only limiting closure premise concerns the attainable pair consisting of mean
scalar and total traceless-Ricci energy.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

omit [SecondCountableTopology M] in
/-- The global Hausdorff and automatic Lichnerowicz packages supply the actual
moving total-scalar derivative used by the normalized-flow energy identity. -/
theorem GlobalFiniteHausdorffChartScalarVariation.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (H : GlobalFiniteHausdorffChartScalarVariation gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (t : ℝ) :
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t :=
  H.hasDerivAt_totalScalar_energyNumerator hFlow (by norm_num)
    (fun s ↦ scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      (hFlow s) (hLichnerowicz.timeVariationEntries s))
    (fun s x ↦ hLichnerowicz.scalarVariation_stokes s x) hStokes t

omit [SecondCountableTopology M] in
/-- The corresponding global Hausdorff volume derivative is automatic from
the normalized-flow equation. -/
theorem GlobalFiniteHausdorffChartScalarVariation.hasDerivAt_totalVolume_of_normalizedFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (H : GlobalFiniteHausdorffChartScalarVariation gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (t : ℝ) :
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t :=
  H.volumeVariation.hasDerivAt_totalVolume t
    (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
      (hFlow t) (by norm_num))

/-- Strongest finite-dissipation endpoint of this route: actual Hausdorff
moving integrals, automatic scalar variation and regularity, and closedness of
only the attainable two-scalar invariant range. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergyRange_of_scalarLower
      gt hFlow
      (hHausdorff.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorff.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      hFiniteDissipation hRangeClosed hc hScalarLower

/-- Exponential domination discharges finite dissipation in the preceding
fully assembled closed-range endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate c : ℝ} (hrate : 0 < rate) (hc : 0 < c)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff hLichnerowicz hStokes
        (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
          gt hDissipationMeasurable hrate hDecay)
        hRangeClosed hc hScalarLower

/-- The same geometric packages also make the quantitative exponential
mean-scalar convergence estimate directly available. -/
theorem abs_meanScalar_sub_normalizedMeanScalarLimit_le_of_exponential_absoluteDissipation_of_globalHausdorffLichnerowiczRegularity
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t)
    (hDecay : ∀ s ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt s ≤
        C * Real.exp ((-rate) * s)) :
    |meanScalar (gt t) - normalizedMeanScalarLimit gt| ≤
      C * Real.exp ((-rate) * t) / rate := by
  let hTotalScalar :=
    hHausdorff.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
      hFlow hLichnerowicz hStokes
  let hVolume := hHausdorff.hasDerivAt_totalVolume_of_normalizedFlow hFlow
  have hMeanDeriv : ∀ s : ℝ,
      HasDerivAt (fun q ↦ meanScalar (gt q))
        (deriv (fun q ↦ meanScalar (gt q)) s) s := by
    intro s
    exact (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
      (hFlow s) (by norm_num) (hTotalScalar s) (hVolume s)).differentiableAt.hasDerivAt
  exact
    abs_meanScalar_sub_normalizedMeanScalarLimit_le_of_exponential_absoluteDissipation
      gt hMeanDeriv
        (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
          gt hDissipationMeasurable hrate hDecay)
        hrate ht hDecay

end Poincare
