import Poincare.Global.NormalizedFlowAbsoluteDissipation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Forward-time absolute-dissipation extraction

The normalized-flow endpoint in `NormalizedFlowAbsoluteDissipation` is stated
for a metric path solving the equation at every real time.  Geometric Ricci
flows are naturally supplied only on the forward ray `Ici 0`.

This module keeps the existing all-real interface intact and adds the
forward-time variant.  There are two small domain issues to resolve.

* An escaping sequence is eventually nonnegative, but that is not enough to
  apply hypotheses stated pointwise on `Ici 0`.  We discard a finite prefix
  and reindex the tail, so every selected time is nonnegative while all limits
  are preserved.
* Vanishing total-volume derivative only on `Ici 0` gives constancy on that
  ray, not on all of `Real`.  We prove constancy separately on each compact
  interval between two nonnegative times.

With those two bridges, the absolute-dissipation energy extraction and the
two Hamilton endpoints need flow and moving-integral hypotheses only at
nonnegative times.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Finite absolute dissipation admits an escaping sequence consisting
entirely of nonnegative times.

The original selector already tends to `+∞`.  We use that convergence to
find a tail lying in `Ici 0`, shift the natural-number index by the start of
that tail, and compose each convergence statement with the shift. -/
theorem exists_nonnegative_meanScalar_deriv_and_variance_tendsto_zero_of_finite_absoluteDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
    ∃ sample : ℕ → ℝ,
      (∀ i : ℕ, sample i ∈ Ici (0 : ℝ)) ∧
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) atTop
        (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) := by
  obtain ⟨sample, hsampleAtTop, hDerivativeZero, hVarianceZero⟩ :=
    exists_meanScalar_deriv_and_variance_tendsto_zero_of_finite_absoluteDissipation
      gt hFiniteDissipation
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (hsampleAtTop.eventually_ge_atTop (0 : ℝ))
  let forwardSample : ℕ → ℝ := fun i ↦ sample (i + N)
  refine ⟨forwardSample, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hN (i + N) (by omega)
  · exact hsampleAtTop.comp (tendsto_add_atTop_nat N)
  · exact hDerivativeZero.comp (tendsto_add_atTop_nat N)
  · exact hVarianceZero.comp (tendsto_add_atTop_nat N)

/-- A normalized closed Ricci flow has constant total volume on the
nonnegative ray once the moving-volume derivative is identified there.

The proof deliberately works on the compact interval between two requested
times.  Thus no derivative, flow equation, or extension to negative time is
used. -/
theorem totalVolume_eq_of_closedNormalizedRicciFlow_Ici
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    {s t : ℝ} (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ)) :
    totalVolume (gt s) = totalVolume (gt t) := by
  let V : ℝ → ℝ := fun r ↦ totalVolume (gt r)
  have hzero : ∀ r ∈ Ici (0 : ℝ), HasDerivAt V 0 r := by
    intro r hr
    exact hasDerivAt_totalVolume_zero_of_closedNormalizedRicciFlow
      (hFlow r hr) (by norm_num) (hVolumeVariation r hr)
  have hInterval : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → V a = V b := by
    intro a b ha hab
    have hDifferentiable : DifferentiableOn ℝ V (Icc a b) := by
      intro r hr
      exact (hzero r (ha.trans hr.1)).differentiableAt.differentiableWithinAt
    have hDerivWithin : ∀ r ∈ Ico a b,
        derivWithin V (Icc a b) r = 0 := by
      intro r hr
      exact (hzero r (ha.trans hr.1)).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc (hr.1.trans_lt hr.2) r ⟨hr.1, hr.2.le⟩)
    have hConstant :=
      constant_of_derivWithin_zero hDifferentiable hDerivWithin
    exact (hConstant b ⟨hab, le_rfl⟩).symm
  rcases le_total s t with hst | hts
  · exact hInterval hs hst
  · exact (hInterval ht hts).symm

/-- Forward-ray version of the three-dimensional absolute-dissipation energy
extraction.  Both the mean-scalar identity and volume constancy are required
only at the selected nonnegative times. -/
theorem exists_normalized_energy_tendsto_zero_of_finite_absoluteDissipation_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hMeanDerivativeEnergy : ∀ t ∈ Ici (0 : ℝ),
      deriv (fun s ↦ meanScalar (gt s)) t =
        normalizedMeanScalarEnergyNumerator (gt t) / totalVolume (gt t))
    (hVolumeConstant : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (gt t) = totalVolume (gt 0)) :
    ∃ sample : ℕ → ℝ,
      (∀ i : ℕ, sample i ∈ Ici (0 : ℝ)) ∧
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) atTop
        (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) := by
  obtain ⟨sample, hsampleNonneg, hsampleAtTop, hDerivativeZero,
      hVarianceZero⟩ :=
    exists_nonnegative_meanScalar_deriv_and_variance_tendsto_zero_of_finite_absoluteDissipation
      gt hFiniteDissipation
  have hVolume :
      Tendsto (fun i ↦ totalVolume (gt (sample i))) atTop
        (nhds (totalVolume (gt 0))) := by
    have hEq : ∀ i : ℕ,
        totalVolume (gt (sample i)) = totalVolume (gt 0) :=
      fun i ↦ hVolumeConstant (sample i) (hsampleNonneg i)
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ totalVolume (gt 0)) atTop
        (nhds (totalVolume (gt 0)))).congr' <|
          Eventually.of_forall fun i ↦ (hEq i).symm
  have hNumeratorZero :
      Tendsto
        (fun i ↦ normalizedMeanScalarEnergyNumerator (gt (sample i))) atTop
        (nhds 0) := by
    have hEq : ∀ i : ℕ,
        normalizedMeanScalarEnergyNumerator (gt (sample i)) =
          deriv (fun t ↦ meanScalar (gt t)) (sample i) *
            totalVolume (gt (sample i)) := by
      intro i
      calc
        normalizedMeanScalarEnergyNumerator (gt (sample i)) =
            (normalizedMeanScalarEnergyNumerator (gt (sample i)) /
                totalVolume (gt (sample i))) *
              totalVolume (gt (sample i)) :=
          (div_mul_cancel₀ _ (totalVolume_ne_zero (gt (sample i)))).symm
        _ = deriv (fun t ↦ meanScalar (gt t)) (sample i) *
              totalVolume (gt (sample i)) := by
          rw [hMeanDerivativeEnergy (sample i) (hsampleNonneg i)]
    have hProductZero :
        Tendsto
          (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i) *
            totalVolume (gt (sample i))) atTop (nhds 0) := by
      simpa only [zero_mul] using hDerivativeZero.mul hVolume
    exact hProductZero.congr' <|
      Eventually.of_forall fun i ↦ (hEq i).symm
  have hTwoEnergyZero :
      Tendsto
        (fun i ↦ 2 *
          (∫ x, (gt (sample i)).tracelessRicciNormSqAt x
            ∂(volumeMeasure (gt (sample i))))) atTop (nhds 0) := by
    have hThirdVarianceZero :
        Tendsto
          (fun i ↦ (1 / 3 : ℝ) *
            (∫ x,
              ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
              ∂(volumeMeasure (gt (sample i))))) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hVarianceZero :
        Tendsto
          (fun i : ℕ ↦ (1 / 3 : ℝ) *
            (∫ x,
              ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
              ∂(volumeMeasure (gt (sample i))))) atTop
          (nhds ((1 / 3 : ℝ) * 0)))
    have hSumZero := hNumeratorZero.add hThirdVarianceZero
    simpa only [normalizedMeanScalarEnergyNumerator_three, sub_add_cancel,
      zero_add] using hSumZero
  have hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) := by
    have hHalf :
        Tendsto
          (fun i : ℕ ↦ (2 : ℝ)⁻¹ *
            (2 * (∫ x, (gt (sample i)).tracelessRicciNormSqAt x
              ∂(volumeMeasure (gt (sample i)))))) atTop
          (nhds ((2 : ℝ)⁻¹ * 0)) :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (2 : ℝ)⁻¹) atTop (nhds (2 : ℝ)⁻¹)).mul
          hTwoEnergyZero
    simpa only [← mul_assoc, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      one_mul, mul_zero] using hHalf
  exact ⟨sample, hsampleNonneg, hsampleAtTop, hDerivativeZero,
    hVarianceZero, hEnergyZero⟩

/-- Fully expanded forward normalized-flow extraction.  The flow equation
and moving-integral derivative identities are needed only on `Ici 0`. -/
theorem exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
    ∃ sample : ℕ → ℝ,
      (∀ i : ℕ, sample i ∈ Ici (0 : ℝ)) ∧
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) atTop
        (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) := by
  apply exists_normalized_energy_tendsto_zero_of_finite_absoluteDissipation_Ici
    gt hFiniteDissipation
  · intro t ht
    exact (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
      (hFlow t ht) (by norm_num) (hDifferentiateMovingTotalScalar t ht)
        (hDifferentiateMovingVolume t ht)).deriv
  · intro t ht
    exact totalVolume_eq_of_closedNormalizedRicciFlow_Ici
      (s := t) (t := 0) hFlow hDifferentiateMovingVolume ht
        (by norm_num : (0 : ℝ) ∈ Ici (0 : ℝ))

/-- Forward-time Hamilton endpoint from finite absolute dissipation and a
uniform positive mean-scalar lower bound. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_Ici_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t ∈ Ici (0 : ℝ), c ≤ meanScalar (gt t)) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsampleNonneg, hsampleAtTop, _hDerivativeZero,
      _hVarianceZero, hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation_Ici
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  obtain ⟨gLimit, hMeanLimit, hEnergyLimit⟩ :=
    hCompact.extract sample hsampleAtTop
  have hLimitEnergy :
      (∫ x, gLimit.tracelessRicciNormSqAt x ∂(volumeMeasure gLimit)) = 0 :=
    tendsto_nhds_unique hEnergyLimit hEnergyZero
  have hLimitMeanLower : c ≤ meanScalar gLimit :=
    ge_of_tendsto hMeanLimit <|
      Eventually.of_forall fun i ↦ hMeanLower (sample i) (hsampleNonneg i)
  have hMeanPos : 0 < meanScalar gLimit := hc.trans_le hLimitMeanLower
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    gLimit hLimitEnergy hMeanPos

/-- A positive pointwise scalar-curvature lower bound on `Ici 0` supplies the
mean lower bound in the forward absolute-dissipation Hamilton endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_Ici_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_Ici_of_meanLower
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation hCompact hc
  intro t ht
  exact le_meanScalar_of_forall_le_scalarAt (gt t) c (hScalarLower t ht)

end Poincare
