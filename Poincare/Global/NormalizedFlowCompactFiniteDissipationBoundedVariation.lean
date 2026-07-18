import Poincare.Global.NormalizedFlowCompactScalarVarianceContinuity
import Poincare.Global.NormalizedFlowForwardTracelessEnergyDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite normalized-flow dissipation from bounded mean-scalar variation

For a three-dimensional normalized Ricci flow, let `E` be the total squared
traceless-Ricci curvature and let `V` be the scalar-curvature variance.  The
exact mean-scalar identity and constant total volume give

`V = 6 * E - 3 * volume * mean'`.

Integrating this identity on `[0, T]`, a finite forward integral of `E` and a
uniform lower bound for the mean scalar give a uniform upper bound for the
nonnegative integrals of `V`.  Monotone exhaustion of the forward ray then
makes `V` integrable.  The same identity makes `mean'` integrable, and hence
the full absolute mean-scalar/variance dissipation is integrable.

This argument uses neither a sign condition on `mean'` nor a pointwise
scalar-variance/traceless-energy gap.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Finite total traceless-Ricci energy and a lower bound for the mean scalar
force finite total scalar variance on the forward ray.

Continuity of the two curvature tracks is used only for finite-interval
integrability and measurability.  In applications it is supplied by a compact
parameterization of the metric orbit. -/
theorem normalizedFlowScalarVarianceTrack_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower_of_continuousTracks
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hEnergyContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (hVarianceContinuous : ContinuousOn
      (normalizedFlowScalarVarianceTrack gt) (Ici 0))
    (hEnergyIntegrable : IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    {scalarFloor : ℝ}
    (hMeanLower : ∀ t : Ici (0 : ℝ),
      scalarFloor ≤ meanScalar (gt t.1)) :
    IntegrableOn (normalizedFlowScalarVarianceTrack gt) (Ici 0) := by
  let f : ℝ → ℝ := fun t ↦ meanScalar (gt t)
  let energy : ℝ → ℝ := normalizedFlowTracelessRicciEnergyTrack gt
  let variance : ℝ → ℝ := normalizedFlowScalarVarianceTrack gt
  let volume0 : ℝ := totalVolume (gt 0)
  let derivativeModel : ℝ → ℝ := fun t ↦
    (2 * energy t - (1 / 3 : ℝ) * variance t) / volume0
  have hVolume0Pos : 0 < volume0 := by
    dsimp only [volume0]
    exact totalVolume_pos (gt 0)
  have hVolumeConstant : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (gt t) = volume0 := by
    intro t ht
    dsimp only [volume0]
    exact totalVolume_eq_of_closedNormalizedRicciFlow_Ici
      (s := t) (t := 0)
      (fun r hr ↦ hFlow ⟨r, hr⟩)
      (fun r hr ↦ hDifferentiateMovingVolume ⟨r, hr⟩)
      ht (by norm_num)
  have hHasDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt f (derivativeModel t) t := by
    intro t ht
    have h := hasDerivAt_meanScalar_three_of_normalizedFlow
      (hFlow ⟨t, ht⟩)
      (hDifferentiateMovingTotalScalar ⟨t, ht⟩)
      (hDifferentiateMovingVolume ⟨t, ht⟩)
    simpa only [f, derivativeModel, energy, variance,
      normalizedFlowTracelessRicciEnergyTrack,
      normalizedFlowScalarVarianceTrack, hVolumeConstant t ht] using h
  have hDerivativeModelContinuous : ContinuousOn derivativeModel (Ici 0) := by
    dsimp only [derivativeModel, energy, variance]
    exact
      ((hEnergyContinuous.const_mul 2).sub
        (hVarianceContinuous.const_mul (1 / 3))).div_const volume0
  have hVarianceEq : ∀ t ∈ Ici (0 : ℝ),
      variance t = 6 * energy t - 3 * volume0 * derivativeModel t := by
    intro t _ht
    dsimp only [derivativeModel]
    field_simp [ne_of_gt hVolume0Pos]; ring
  have hEnergyNonneg : ∀ t : ℝ, 0 ≤ energy t := by
    intro t
    exact normalizedFlowTracelessRicciEnergyTrack_nonneg gt t
  have hVarianceNonneg : ∀ t : ℝ, 0 ≤ variance t := by
    intro t
    exact centeredScalarSqIntegral_nonneg (gt t)
  let bound : ℝ :=
    6 * (∫ t in Ici (0 : ℝ), energy t) +
      3 * volume0 * (f 0 - scalarFloor)
  have hFiniteIntervalIntegrable : ∀ n : ℕ,
      IntegrableOn variance (Ico (0 : ℝ) (n : ℝ)) := by
    intro n
    have hIcc : IntegrableOn variance (Icc (0 : ℝ) (n : ℝ)) := by
      apply ContinuousOn.integrableOn_Icc
      exact hVarianceContinuous.mono fun _t ht ↦ ht.1
    exact hIcc.mono_set Ico_subset_Icc_self
  have hFiniteIntervalBound : ∀ n : ℕ,
      (∫ t in Ico (0 : ℝ) (n : ℝ), variance t) ≤ bound := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hIntervalSubset : Icc (0 : ℝ) (n : ℝ) ⊆ Ici (0 : ℝ) :=
      fun _t ht ↦ ht.1
    have hEnergyInterval : IntervalIntegrable energy MeasureTheory.volume 0 (n : ℝ) :=
      (hEnergyContinuous.mono hIntervalSubset).intervalIntegrable_of_Icc hn
    have hVarianceInterval : IntervalIntegrable variance MeasureTheory.volume 0 (n : ℝ) :=
      (hVarianceContinuous.mono hIntervalSubset).intervalIntegrable_of_Icc hn
    have hDerivativeInterval :
        IntervalIntegrable derivativeModel MeasureTheory.volume 0 (n : ℝ) :=
      (hDerivativeModelContinuous.mono hIntervalSubset).intervalIntegrable_of_Icc hn
    have hFTC : (∫ t in (0 : ℝ)..(n : ℝ), derivativeModel t) =
        f (n : ℝ) - f 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht ↦ hHasDeriv t (hIntervalSubset <| by simpa [uIcc_of_le hn] using ht))
        hDerivativeInterval
    have hVarianceIntegralEq :
        (∫ t in (0 : ℝ)..(n : ℝ), variance t) =
          6 * (∫ t in (0 : ℝ)..(n : ℝ), energy t) -
            3 * volume0 * (f (n : ℝ) - f 0) := by
      calc
        (∫ t in (0 : ℝ)..(n : ℝ), variance t) =
            ∫ t in (0 : ℝ)..(n : ℝ),
              (6 * energy t - 3 * volume0 * derivativeModel t) := by
                apply intervalIntegral.integral_congr
                intro t ht
                exact hVarianceEq t (hIntervalSubset <| by
                  simpa [uIcc_of_le hn] using ht)
        _ = 6 * (∫ t in (0 : ℝ)..(n : ℝ), energy t) -
              3 * volume0 *
                (∫ t in (0 : ℝ)..(n : ℝ), derivativeModel t) := by
              rw [intervalIntegral.integral_sub
                (hEnergyInterval.const_mul 6)
                (hDerivativeInterval.const_mul (3 * volume0)),
                intervalIntegral.integral_const_mul,
                intervalIntegral.integral_const_mul]
        _ = 6 * (∫ t in (0 : ℝ)..(n : ℝ), energy t) -
              3 * volume0 * (f (n : ℝ) - f 0) := by rw [hFTC]
    have hEnergyIntervalLe :
        (∫ t in (0 : ℝ)..(n : ℝ), energy t) ≤
          ∫ t in Ici (0 : ℝ), energy t := by
      rw [intervalIntegral.integral_of_le hn]
      exact setIntegral_mono_set hEnergyIntegrable
        (ae_of_all _ hEnergyNonneg)
        (show Ioc (0 : ℝ) (n : ℝ) ⊆ Ici (0 : ℝ) from
          fun _t ht ↦ ht.1.le).eventuallyLE
    have hMeanN : scalarFloor ≤ f (n : ℝ) := by
      simpa only [f] using hMeanLower ⟨(n : ℝ), hn⟩
    have hSetIntegralEq :
        (∫ t in Ico (0 : ℝ) (n : ℝ), variance t) =
          ∫ t in (0 : ℝ)..(n : ℝ), variance t := by
      rw [intervalIntegral.integral_of_le hn]
      exact integral_Ico_eq_integral_Ioc
    rw [hSetIntegralEq, hVarianceIntegralEq]
    dsimp only [bound]
    nlinarith [hVolume0Pos, hEnergyIntervalLe, hMeanN]
  have hCover : AECover
      (MeasureTheory.volume.restrict (Ici (0 : ℝ))) atTop
      (fun n : ℕ ↦ Ico (0 : ℝ) (n : ℝ)) :=
    aecover_Ici_of_Ico (B := (0 : ℝ))
      (d := fun n : ℕ ↦ (n : ℝ)) tendsto_natCast_atTop_atTop
  have hVarianceIntegrableRestricted : Integrable variance
      (MeasureTheory.volume.restrict (Ici (0 : ℝ))) := by
    apply hCover.integrable_of_integral_bounded_of_nonneg_ae bound
    · intro n
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ico,
        inter_eq_left.2 Ico_subset_Ici_self]
      exact hFiniteIntervalIntegrable n
    · exact ae_of_all _ hVarianceNonneg
    · filter_upwards with n
      simpa [Measure.restrict_restrict measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ico,
        inter_eq_left.2 Ico_subset_Ici_self] using hFiniteIntervalBound n
  simpa only [IntegrableOn] using hVarianceIntegrableRestricted

/-- Bounded mean-scalar variation converts finite traceless-Ricci energy into
finite absolute mean-scalar/variance dissipation. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower_of_continuousTracks
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hEnergyContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (hVarianceContinuous : ContinuousOn
      (normalizedFlowScalarVarianceTrack gt) (Ici 0))
    (hEnergyIntegrable : IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    {scalarFloor : ℝ}
    (hMeanLower : ∀ t : Ici (0 : ℝ),
      scalarFloor ≤ meanScalar (gt t.1)) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) := by
  let f : ℝ → ℝ := fun t ↦ meanScalar (gt t)
  let energy : ℝ → ℝ := normalizedFlowTracelessRicciEnergyTrack gt
  let variance : ℝ → ℝ := normalizedFlowScalarVarianceTrack gt
  let volume0 : ℝ := totalVolume (gt 0)
  have hVarianceIntegrable : IntegrableOn variance (Ici 0) := by
    simpa only [variance] using
      normalizedFlowScalarVarianceTrack_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower_of_continuousTracks
        gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hEnergyContinuous hVarianceContinuous hEnergyIntegrable hMeanLower
  have hVolumeConstant : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (gt t) = volume0 := by
    intro t ht
    dsimp only [volume0]
    exact totalVolume_eq_of_closedNormalizedRicciFlow_Ici
      (s := t) (t := 0)
      (fun r hr ↦ hFlow ⟨r, hr⟩)
      (fun r hr ↦ hDifferentiateMovingVolume ⟨r, hr⟩)
      ht (by norm_num)
  have hDerivativeEq : ∀ t ∈ Ici (0 : ℝ),
      deriv f t =
        (2 * energy t - (1 / 3 : ℝ) * variance t) / volume0 := by
    intro t ht
    have h :=
      (hasDerivAt_meanScalar_three_of_normalizedFlow
        (hFlow ⟨t, ht⟩)
        (hDifferentiateMovingTotalScalar ⟨t, ht⟩)
        (hDifferentiateMovingVolume ⟨t, ht⟩)).deriv
    simpa only [f, energy, variance,
      normalizedFlowTracelessRicciEnergyTrack,
      normalizedFlowScalarVarianceTrack, hVolumeConstant t ht] using h
  have hDerivativeModelIntegrable : IntegrableOn
      (fun t ↦ (2 * energy t - (1 / 3 : ℝ) * variance t) / volume0)
      (Ici 0) :=
    ((hEnergyIntegrable.const_mul 2).sub
      (hVarianceIntegrable.const_mul (1 / 3))).div_const volume0
  have hDerivativeIntegrable : IntegrableOn (deriv f) (Ici 0) :=
    hDerivativeModelIntegrable.congr_fun
      (fun t ht ↦ (hDerivativeEq t ht).symm) measurableSet_Ici
  have hAbsoluteDerivativeIntegrable : IntegrableOn
      (fun t ↦ |deriv f t|) (Ici 0) := by
    simpa only [Real.norm_eq_abs] using hDerivativeIntegrable.norm
  have hSum : IntegrableOn
      (fun t ↦ |deriv f t| + variance t) (Ici 0) :=
    hAbsoluteDerivativeIntegrable.add hVarianceIntegrable
  exact hSum.congr_fun (fun t _ht ↦ by
    rfl) measurableSet_Ici

variable {K : Type v} [TopologicalSpace K]

/-- Compact-orbit form of the bounded-variation finite-dissipation theorem.

Weak continuity of the moving volume measures and joint continuity of scalar
curvature and squared traceless-Ricci norm provide all time-track continuity
needed by the analytic argument. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_parameterization_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hParameter : Continuous parameter)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2))
    (hTracelessRicci : Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2))
    (hEnergyIntegrable : IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    {scalarFloor : ℝ}
    (hMeanLower : ∀ t : Ici (0 : ℝ),
      scalarFloor ≤ meanScalar (gt t.1)) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) := by
  have hEnergyContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) :=
    continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
      gt metric parameter hParameter hRealizes hMeasure hTracelessRicci
  have hVarianceContinuous : ContinuousOn
      (normalizedFlowScalarVarianceTrack gt) (Ici 0) :=
    continuousOn_normalizedFlowScalarVarianceTrack_of_parameterization
      gt metric parameter hParameter hRealizes hMeasure hScalar
  exact
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower_of_continuousTracks
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hEnergyContinuous hVarianceContinuous hEnergyIntegrable hMeanLower

end Poincare
