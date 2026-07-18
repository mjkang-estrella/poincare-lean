import Poincare.Global.NormalizedFlowFiniteDissipationLimit
import Mathlib.MeasureTheory.Integral.Average

/-!
# Absolute-dissipation extraction for normalized Ricci flow

The earlier finite-dissipation extraction uses
`deriv meanScalar + scalarVariance`.  Its nonnegativity is obtained from
monotonicity of the mean scalar, and bounded monotonicity is then used to
identify a mean-scalar limit.

For the geometric energy endpoint, neither hypothesis is needed.  Replacing
the derivative by its absolute value makes the dissipation manifestly
nonnegative.  Finite integrability alone then selects escaping
times at which both the derivative and the scalar variance tend to zero.  In
dimension three, the exact normalized mean-scalar identity and constant total
volume force the traceless-Ricci energy to tend to zero on the same sequence.

The final theorem combines this extraction with the repository's scalar-energy
sequential compactness interface.  A uniform positive lower bound for the mean
scalar passes to the extracted smooth limit and supplies Hamilton's reduced
positive-Einstein core.
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

/-- Absolute mean-scalar dissipation plus scalar-curvature variance.

Unlike `normalizedMeanScalarVarianceDissipation`, this quantity is
nonnegative without any monotonicity assumption on the mean scalar. -/
def normalizedMeanScalarAbsoluteVarianceDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) : ℝ :=
  |deriv (fun s ↦ meanScalar (gt s)) t| +
    ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
      ∂(volumeMeasure (gt t))

/-- Absolute mean-scalar/variance dissipation is pointwise nonnegative. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_nonneg
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) :
    0 ≤ normalizedMeanScalarAbsoluteVarianceDissipation gt t := by
  unfold normalizedMeanScalarAbsoluteVarianceDissipation
  exact add_nonneg (abs_nonneg _) (centeredScalarSqIntegral_nonneg (gt t))

/-- A continuous integrable function on the nonnegative ray has values tending
to zero along a sequence containing one point in each successive unit
interval.

No sign hypothesis is required for this selection lemma.  The mean-value
theorem identifies a point value with the unit-interval integral, while
integrability makes the tails, hence those unit-interval integrals, vanish. -/
theorem exists_escaping_sample_value_tendsto_zero_of_continuousOn_integrableOn
    (D : ℝ → ℝ)
    (hContinuous : ContinuousOn D (Ici 0))
    (hIntegrable : IntegrableOn D (Ici 0)) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto (fun n ↦ D (sample n)) atTop (nhds 0) := by
  have hSelect : ∀ n : ℕ, ∃ c : ℝ,
      c ∈ uIcc (n : ℝ) ((n : ℝ) + 1) ∧
        (∫ t in (n : ℝ)..((n : ℝ) + 1), D t) = D c := by
    intro n
    have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hIntervalSubset : uIcc (n : ℝ) ((n : ℝ) + 1) ⊆ Ici (0 : ℝ) := by
      rw [uIcc_of_le hn]
      intro t ht
      exact (Nat.cast_nonneg n).trans ht.1
    obtain ⟨c, hc, hmean⟩ :=
      exists_eq_const_mul_intervalIntegral_of_nonneg
        (hContinuous.mono hIntervalSubset)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (1 : ℝ)))
        (fun _ _ ↦ zero_le_one)
    refine ⟨c, hc, ?_⟩
    simpa only [mul_one, intervalIntegral.integral_const, sub_self,
      add_sub_cancel_left, one_smul] using hmean
  choose sample hsample hsampleMean using hSelect
  have hsampleLower : ∀ n : ℕ, (n : ℝ) ≤ sample n := by
    intro n
    have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    simpa only [min_eq_left hn] using (hsample n).1
  have hsampleAtTop : Tendsto sample atTop atTop :=
    tendsto_atTop_mono hsampleLower tendsto_natCast_atTop_atTop
  have hNatAddAtTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hTail :
      Tendsto (fun n : ℕ ↦ ∫ t in Ici (n : ℝ), D t) atTop (nhds 0) :=
    tendsto_integral_Ici_zero tendsto_natCast_atTop_atTop
  have hTailAdd :
      Tendsto (fun n : ℕ ↦ ∫ t in Ici ((n : ℝ) + 1), D t) atTop
        (nhds 0) :=
    tendsto_integral_Ici_zero hNatAddAtTop
  have hUnitIntegral :
      Tendsto (fun n : ℕ ↦ ∫ t in (n : ℝ)..((n : ℝ) + 1), D t)
        atTop (nhds 0) := by
    have hTailDiff := hTail.sub hTailAdd
    have hEq : ∀ n : ℕ,
        (∫ t in Ici (n : ℝ), D t) -
            (∫ t in Ici ((n : ℝ) + 1), D t) =
          ∫ t in (n : ℝ)..((n : ℝ) + 1), D t := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      exact intervalIntegral.integral_Ici_sub_Ici'
        (hIntegrable.mono_set (Ici_subset_Ici.2 hn0))
        (hIntegrable.mono_set (Ici_subset_Ici.2 hn1))
    simpa only [sub_zero] using
      hTailDiff.congr' (Eventually.of_forall hEq)
  have hValueZero : Tendsto (fun n ↦ D (sample n)) atTop (nhds 0) :=
    hUnitIntegral.congr' <|
      Eventually.of_forall fun n ↦ hsampleMean n
  exact ⟨sample, hsampleAtTop, hValueZero⟩

/-- Stronger first-moment selection: a nonnegative integrable function on the
nonnegative ray has values tending to zero along escaping unit-interval
samples, with no continuity hypothesis.

On each interval `(n, n + 1]`, Mathlib's first-moment theorem supplies a point
where the function is at most its average.  The interval has volume one, and
the averages tend to zero because they are differences of integrable tails. -/
theorem exists_escaping_sample_value_tendsto_zero_of_integrableOn_nonneg
    (D : ℝ → ℝ)
    (hNonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ D t)
    (hIntegrable : IntegrableOn D (Ici 0)) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto (fun n ↦ D (sample n)) atTop (nhds 0) := by
  have hSelect : ∀ n : ℕ, ∃ c : ℝ,
      c ∈ Ioc (n : ℝ) ((n : ℝ) + 1) ∧
        D c ≤ ∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), D t := by
    intro n
    let J : Set ℝ := Ioc (n : ℝ) ((n : ℝ) + 1)
    have hJSubset : J ⊆ Ici (0 : ℝ) := by
      intro t ht
      exact (Nat.cast_nonneg n).trans ht.1.le
    have hJIntegrable : IntegrableOn D J :=
      hIntegrable.mono_set hJSubset
    have hJne : MeasureTheory.volume J ≠ 0 := by
      simp [J]
    have hJtop : MeasureTheory.volume J ≠ (⊤ : ℝ≥0∞) := by
      simp [J, Real.volume_Ioc]
    obtain ⟨c, hcJ, hc⟩ :=
      exists_le_setAverage hJne hJtop hJIntegrable
    refine ⟨c, hcJ, ?_⟩
    have hAverage :
        (⨍ t in J, D t ∂MeasureTheory.volume) =
          ∫ t in J, D t ∂MeasureTheory.volume := by
      rw [setAverage_eq]
      simp [J]
    simpa [hAverage] using hc
  choose sample hsample hsampleLe using hSelect
  have hsampleLower : ∀ n : ℕ, (n : ℝ) ≤ sample n := by
    intro n
    exact (hsample n).1.le
  have hsampleAtTop : Tendsto sample atTop atTop :=
    tendsto_atTop_mono hsampleLower tendsto_natCast_atTop_atTop
  have hNatAddAtTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hTail :
      Tendsto (fun n : ℕ ↦ ∫ t in Ici (n : ℝ), D t) atTop (nhds 0) :=
    tendsto_integral_Ici_zero tendsto_natCast_atTop_atTop
  have hTailAdd :
      Tendsto (fun n : ℕ ↦ ∫ t in Ici ((n : ℝ) + 1), D t) atTop
        (nhds 0) :=
    tendsto_integral_Ici_zero hNatAddAtTop
  have hUnitIntegral :
      Tendsto
        (fun n : ℕ ↦ ∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), D t)
        atTop (nhds 0) := by
    have hTailDiff := hTail.sub hTailAdd
    have hEq : ∀ n : ℕ,
        (∫ t in Ici (n : ℝ), D t) -
            (∫ t in Ici ((n : ℝ) + 1), D t) =
          ∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), D t := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      calc
        (∫ t in Ici (n : ℝ), D t) -
            (∫ t in Ici ((n : ℝ) + 1), D t) =
            ∫ t in (n : ℝ)..((n : ℝ) + 1), D t :=
          intervalIntegral.integral_Ici_sub_Ici'
            (hIntegrable.mono_set (Ici_subset_Ici.2 hn0))
            (hIntegrable.mono_set (Ici_subset_Ici.2 hn1))
        _ = ∫ t in Ioc (n : ℝ) ((n : ℝ) + 1), D t :=
          intervalIntegral.integral_of_le hn
    simpa only [sub_zero] using
      hTailDiff.congr' (Eventually.of_forall hEq)
  have hSampleNonneg : ∀ n : ℕ, 0 ≤ D (sample n) := by
    intro n
    exact hNonneg (sample n)
      ((Nat.cast_nonneg n).trans (hsample n).1.le)
  have hValueZero : Tendsto (fun n ↦ D (sample n)) atTop (nhds 0) :=
    squeeze_zero hSampleNonneg hsampleLe hUnitIntegral
  exact ⟨sample, hsampleAtTop, hValueZero⟩

/-- Finite absolute dissipation selects escaping times at which
both the mean-scalar derivative and scalar-curvature variance tend to zero.

There is no continuity, monotonicity, or boundedness assumption on the mean
scalar or on the dissipation. -/
theorem exists_meanScalar_deriv_and_variance_tendsto_zero_of_finite_absoluteDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) atTop
        (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) := by
  let D : ℝ → ℝ := normalizedMeanScalarAbsoluteVarianceDissipation gt
  obtain ⟨sample, hsampleAtTop, hDissipationZero⟩ :=
    exists_escaping_sample_value_tendsto_zero_of_integrableOn_nonneg D
      (fun t _ht ↦ by
        dsimp only [D]
        exact normalizedMeanScalarAbsoluteVarianceDissipation_nonneg gt t)
      hFiniteDissipation
  have hAbsDerivativeNonneg : ∀ n : ℕ,
      0 ≤ |deriv (fun t ↦ meanScalar (gt t)) (sample n)| :=
    fun _ ↦ abs_nonneg _
  have hVarianceNonneg : ∀ n : ℕ,
      0 ≤ ∫ x,
        ((gt (sample n)).scalarAt x - meanScalar (gt (sample n))) ^ 2
        ∂(volumeMeasure (gt (sample n))) :=
    fun n ↦ centeredScalarSqIntegral_nonneg (gt (sample n))
  have hAbsDerivativeLe : ∀ n : ℕ,
      |deriv (fun t ↦ meanScalar (gt t)) (sample n)| ≤ D (sample n) := by
    intro n
    dsimp only [D, normalizedMeanScalarAbsoluteVarianceDissipation]
    linarith [hVarianceNonneg n]
  have hVarianceLe : ∀ n : ℕ,
      (∫ x, ((gt (sample n)).scalarAt x - meanScalar (gt (sample n))) ^ 2
        ∂(volumeMeasure (gt (sample n)))) ≤ D (sample n) := by
    intro n
    dsimp only [D, normalizedMeanScalarAbsoluteVarianceDissipation]
    linarith [hAbsDerivativeNonneg n]
  have hAbsDerivativeZero :
      Tendsto
        (fun n ↦ |deriv (fun t ↦ meanScalar (gt t)) (sample n)|) atTop
        (nhds 0) :=
    squeeze_zero hAbsDerivativeNonneg hAbsDerivativeLe hDissipationZero
  have hDerivativeZero :
      Tendsto
        (fun n ↦ deriv (fun t ↦ meanScalar (gt t)) (sample n)) atTop
        (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hAbsDerivativeZero
  have hVarianceZero :
      Tendsto
        (fun n ↦ ∫ x,
          ((gt (sample n)).scalarAt x - meanScalar (gt (sample n))) ^ 2
          ∂(volumeMeasure (gt (sample n)))) atTop (nhds 0) :=
    squeeze_zero hVarianceNonneg hVarianceLe hDissipationZero
  exact ⟨sample, hsampleAtTop, hDerivativeZero, hVarianceZero⟩

/-- Along the absolute-dissipation sequence, the exact three-dimensional
normalized mean-scalar identity and constant total volume force the total
traceless-Ricci energy to tend to zero as well. -/
theorem exists_normalized_energy_tendsto_zero_of_finite_absoluteDissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hMeanDerivativeEnergy : ∀ t : ℝ,
      deriv (fun s ↦ meanScalar (gt s)) t =
        normalizedMeanScalarEnergyNumerator (gt t) / totalVolume (gt t))
    (hVolumeConstant : ∀ t : ℝ,
      totalVolume (gt t) = totalVolume (gt 0)) :
    ∃ sample : ℕ → ℝ,
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
  obtain ⟨sample, hsampleAtTop, hDerivativeZero, hVarianceZero⟩ :=
    exists_meanScalar_deriv_and_variance_tendsto_zero_of_finite_absoluteDissipation
      gt hFiniteDissipation
  have hVolume :
      Tendsto (fun i ↦ totalVolume (gt (sample i))) atTop
        (nhds (totalVolume (gt 0))) := by
    simpa only [hVolumeConstant] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ totalVolume (gt 0)) atTop
          (nhds (totalVolume (gt 0))))
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
          rw [hMeanDerivativeEnergy (sample i)]
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
  exact ⟨sample, hsampleAtTop, hDerivativeZero, hVarianceZero, hEnergyZero⟩

/-- Fully expanded normalized-flow extraction from finite absolute
dissipation.  The flow equation and moving-integral derivative identities
supply the exact mean-scalar energy formula and constant total volume. -/
theorem exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation
    [Nonempty M]
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
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
    ∃ sample : ℕ → ℝ,
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
  apply exists_normalized_energy_tendsto_zero_of_finite_absoluteDissipation
    gt hFiniteDissipation
  · intro t
    exact (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
      (hFlow t) (by norm_num) (hDifferentiateMovingTotalScalar t)
        (hDifferentiateMovingVolume t)).deriv
  · intro t
    exact totalVolume_eq_of_closedNormalizedRicciFlow
      hFlow (by norm_num) hDifferentiateMovingVolume t 0

/-- Finite absolute dissipation, scalar-energy sequential compactness, and a
uniform positive mean-scalar lower bound produce Hamilton's reduced
positive-Einstein core.  No monotonicity or upper bound for the mean scalar is
assumed. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_meanLower
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
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c) (hMeanLower : ∀ t : ℝ, c ≤ meanScalar (gt t)) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsampleAtTop, _hDerivativeZero, _hVarianceZero,
      hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  obtain ⟨gLimit, hMeanLimit, hEnergyLimit⟩ :=
    hCompact.extract sample hsampleAtTop
  have hLimitEnergy :
      (∫ x, gLimit.tracelessRicciNormSqAt x ∂(volumeMeasure gLimit)) = 0 :=
    tendsto_nhds_unique hEnergyLimit hEnergyZero
  have hLimitMeanLower : c ≤ meanScalar gLimit :=
    ge_of_tendsto hMeanLimit <|
      Eventually.of_forall fun i ↦ hMeanLower (sample i)
  have hMeanPos : 0 < meanScalar gLimit := hc.trans_le hLimitMeanLower
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    gLimit hLimitEnergy hMeanPos

/-- A uniform positive pointwise scalar-curvature lower bound is a concrete
geometric source of the mean-scalar lower bound used by the absolute-
dissipation Hamilton endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_scalarLower
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
    (hCompact : NormalizedFlowScalarEnergySequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_meanLower
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation hCompact hc
  intro t
  exact le_meanScalar_of_forall_le_scalarAt (gt t) c (hScalarLower t)

end Poincare
