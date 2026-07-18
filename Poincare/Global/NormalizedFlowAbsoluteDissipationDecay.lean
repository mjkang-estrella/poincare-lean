import Poincare.Global.NormalizedFlowLowerSemicontinuousCompactness
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Quantitative decay implies finite absolute dissipation

An exponentially decaying upper bound is a concrete sufficient condition for
the finite absolute-dissipation input of the normalized-flow Hamilton
endpoint.  This module records that analytic bridge and composes it with the
Hausdorff-volume and lower-semicontinuous compactness reductions.
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

/-- Exponential domination on the nonnegative time ray makes the absolute
mean-scalar/variance dissipation integrable. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t)) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) := by
  have hExpIoi : IntegrableOn (fun t : ℝ ↦ Real.exp ((-rate) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hExpIci : IntegrableOn (fun t : ℝ ↦ Real.exp ((-rate) * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hExpIoi
  have hDominating : IntegrableOn
      (fun t : ℝ ↦ C * Real.exp ((-rate) * t)) (Ici 0) :=
    hExpIci.const_mul C
  apply hDominating.mono' hMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (normalizedMeanScalarAbsoluteVarianceDissipation_nonneg gt t)]
  exact hDecay t ht

/-- Continuity of the moving scalar-variance integral is enough to make the
full absolute dissipation measurable.  The absolute derivative summand needs
no geometric regularity premise: derivatives of real functions are already
almost-everywhere strongly measurable. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_aestronglyMeasurable_of_continuousOn_scalarVariance
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hScalarVarianceContinuous : ContinuousOn
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t)))
      (Ici 0)) :
    AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)) := by
  have hDerivativeMeasurable : AEStronglyMeasurable
      (deriv fun t ↦ meanScalar (gt t))
      (MeasureTheory.volume.restrict (Ici 0)) :=
    aestronglyMeasurable_deriv (fun t ↦ meanScalar (gt t))
      (MeasureTheory.volume.restrict (Ici 0))
  have hAbsoluteDerivativeMeasurable : AEStronglyMeasurable
      (fun t ↦ |deriv (fun s ↦ meanScalar (gt s)) t|)
      (MeasureTheory.volume.restrict (Ici 0)) := by
    simpa only [Real.norm_eq_abs] using hDerivativeMeasurable.norm
  have hScalarVarianceMeasurable : AEStronglyMeasurable
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t)))
      (MeasureTheory.volume.restrict (Ici 0)) :=
    hScalarVarianceContinuous.aestronglyMeasurable measurableSet_Ici
  simpa only [normalizedMeanScalarAbsoluteVarianceDissipation] using
    hAbsoluteDerivativeMeasurable.add hScalarVarianceMeasurable

/-- An exponential estimate plus continuity of only the moving
scalar-variance integral gives finite absolute dissipation. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_continuousOn_scalarVariance_of_exponential_bound
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hScalarVarianceContinuous : ContinuousOn
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t)))
      (Ici 0))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t)) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) := by
  exact
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
      gt
      (normalizedMeanScalarAbsoluteVarianceDissipation_aestronglyMeasurable_of_continuousOn_scalarVariance
        gt hScalarVarianceContinuous)
      hrate hDecay

/-- Exponential absolute-dissipation decay can replace the abstract finite-
dissipation premise in the assembled Hausdorff/LSC Hamilton endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffChartDensity_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hHausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt)
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate c : ℝ} (hrate : 0 < rate) (hc : 0 < c)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartDensity_of_lscCompactness
      gt hFlow hDifferentiateMovingTotalScalar hHausdorffVolume
        (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
          gt hDissipationMeasurable hrate hDecay)
        hCompact hc hScalarLower

end Poincare
