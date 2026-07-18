import Poincare.Global.NormalizedFlowAbsoluteDissipation
import Poincare.Global.HausdorffVolumeFirstVariation
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lower-semicontinuous energy compactness endpoint

Smooth compactness need not identify the total traceless-Ricci energy by an
exact limit theorem.  Lower semicontinuity is sufficient because the sampled
energies already converge to zero.  This file weakens the compactness boundary
accordingly and keeps actual Hausdorff volume differentiation in the final
endpoint.
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

/-- Sequential extraction of a smooth candidate with mean-scalar convergence
and lower semicontinuity of total traceless-Ricci energy. -/
structure NormalizedFlowScalarEnergyLscSequentialCompactness
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) where
  extract : ∀ sample : ℕ → ℝ, Tendsto sample atTop atTop →
    ∃ gLimit : ClosedSmoothRiemannianMetric 3 M,
      Tendsto (fun i ↦ meanScalar (gt (sample i))) atTop
        (nhds (meanScalar gLimit)) ∧
      (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit)) ≤
        liminf
          (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
            ∂(volumeMeasure (gt (sample i)))) atTop

/-- Exact scalar-energy sequential compactness implies the weaker
lower-semicontinuous form. -/
def NormalizedFlowScalarEnergySequentialCompactness.toLsc
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (H : NormalizedFlowScalarEnergySequentialCompactness gt) :
    NormalizedFlowScalarEnergyLscSequentialCompactness gt where
  extract sample hsample := by
    obtain ⟨gLimit, hMean, hEnergy⟩ := H.extract sample hsample
    refine ⟨gLimit, hMean, ?_⟩
    rw [hEnergy.liminf_eq]

/-- Finite absolute dissipation plus lower-semicontinuous scalar-energy
compactness already gives a positive Einstein limit. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_lscCompactness_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsampleAtTop, _hDerivativeZero, _hVarianceZero,
      hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  obtain ⟨gLimit, hMeanLimit, hEnergyLsc⟩ :=
    hCompact.extract sample hsampleAtTop
  have hLiminf :
      liminf
          (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
            ∂(volumeMeasure (gt (sample i)))) atTop = 0 :=
    hEnergyZero.liminf_eq
  have hEnergyLe :
      (∫ x, gLimit.tracelessRicciNormSqAt x
        ∂(volumeMeasure gLimit)) ≤ 0 := by
    rw [← hLiminf]
    exact hEnergyLsc
  have hEnergyNonneg :
      0 ≤ ∫ x, gLimit.tracelessRicciNormSqAt x
        ∂(volumeMeasure gLimit) :=
    integral_nonneg fun x ↦
      gLimit.tracelessRicciNormSqAt_nonneg x (by norm_num)
  have hLimitEnergy :
      (∫ x, gLimit.tracelessRicciNormSqAt x
        ∂(volumeMeasure gLimit)) = 0 :=
    le_antisymm hEnergyLe hEnergyNonneg
  have hLimitMeanLower : c ≤ meanScalar gLimit :=
    ge_of_tendsto hMeanLimit <|
      Eventually.of_forall fun i ↦
        le_meanScalar_of_forall_le_scalarAt
          (gt (sample i)) c (hScalarLower (sample i))
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    gLimit hLimitEnergy (hc.trans_le hLimitMeanLower)

/-- The strongest assembled endpoint in this slice: the global finite
Hausdorff chart-density package supplies moving volume differentiation, while
compactness needs only lower semicontinuity of one curvature energy. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartDensity_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hHausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_lscCompactness_of_scalarLower
      gt hFlow hDifferentiateMovingTotalScalar
        (fun t ↦ hHausdorffVolume.hasDerivAt_totalVolume t
          (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
            (hFlow t) (by norm_num)))
        hFiniteDissipation hCompact hc hScalarLower

end Poincare
