import Poincare.Global.NormalizedFlowCompactFixedTargetFiniteTimePositiveEinstein
import Poincare.Global.NormalizedFlowCompactScalarVarianceContinuity
import Poincare.Global.NormalizedFlowForwardFiniteDissipationReduction
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.ForwardTailIntegrability

/-!
# Finite absolute dissipation from a strict scalar-variance energy gap

For a three-dimensional normalized Ricci flow, write

* `V` for the spatial scalar-curvature variance, and
* `E` for the total squared traceless-Ricci curvature.

The exact mean-scalar identity is

`mean' = (2 * E - V / 3) / volume`.

Consequently the non-strict inequality `V ≤ 6 * E` proves only
`mean' ≥ 0`; it does not control either energy because cancellation at the
coefficient `6` is possible.  This file records the honest coercive form.  If
`V ≤ κ * E` for some `0 ≤ κ < 6`, then constant positive volume gives a
pointwise bound

`V ≤ (3 * κ * volume / (6 - κ)) * mean'`.

A finite upper bound for the nondecreasing mean scalar makes `|mean'|`
integrable on the forward ray.  Measurability of `V` and the displayed
coercive bound therefore make the full absolute dissipation integrable.  No
time-integrability hypothesis for `V`, `E`, or the desired dissipation is
assumed.
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

omit [SecondCountableTopology M] in
/-- Bounded nonnegative variation of the mean scalar is integrable on an
arbitrary forward tail `Ici T`.

This is the `Ici T` version of the repository's existing `Ici 0` lemma.  It
is proved directly on the tail, so an eventual coercive gap need not be
extended artificially to earlier times. -/
theorem integrableOn_abs_deriv_meanScalar_of_normalizedFlow_Ici_start_of_deriv_nonneg_of_meanUpper
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {T C : ℝ}
    (hFlow : ∀ t : Ici T, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici T,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici T,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hDerivativeNonneg : ∀ t : Ici T,
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici T, meanScalar (gt t.1) ≤ C) :
    IntegrableOn
      (fun t : ℝ ↦ |deriv (fun s ↦ meanScalar (gt s)) t|)
      (Ici T) := by
  let f : ℝ → ℝ := fun t ↦ meanScalar (gt t)
  have hHasDeriv : ∀ t ∈ Ici T,
      HasDerivAt f (deriv f t) t := by
    intro t ht
    simpa only [f] using
      (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
        (hFlow ⟨t, ht⟩) (by norm_num)
        (hDifferentiateMovingTotalScalar ⟨t, ht⟩)
        (hDifferentiateMovingVolume ⟨t, ht⟩)).differentiableAt.hasDerivAt
  have hContinuous : ContinuousOn f (Ici T) := by
    intro t ht
    exact (hHasDeriv t ht).continuousAt.continuousWithinAt
  have hDifferentiable : DifferentiableOn ℝ f (interior (Ici T)) := by
    intro t ht
    exact
      (hHasDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hDerivativeNonneg' : ∀ t ∈ interior (Ici T),
      0 ≤ deriv f t := by
    intro t ht
    simpa only [f] using hDerivativeNonneg ⟨t, interior_subset ht⟩
  have hMonotone : MonotoneOn f (Ici T) :=
    monotoneOn_of_deriv_nonneg (convex_Ici T) hContinuous
      hDifferentiable hDerivativeNonneg'
  have hImageSubset : f '' Ici T ⊆ Icc (f T) C := by
    rintro y ⟨t, ht, rfl⟩
    constructor
    · exact hMonotone (by simp : T ∈ Ici T) ht ht
    · simpa only [f] using hMeanUpper ⟨t, ht⟩
  have hConstantIntegrable : IntegrableOn
      (fun _ : ℝ ↦ (1 : ℝ)) (f '' Ici T) :=
    (integrableOn_const measure_Icc_lt_top.ne).mono_set hImageSubset
  have hDerivativeIntegrable : IntegrableOn (deriv f) (Ici T) := by
    have h :=
      (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        measurableSet_Ici
        (fun t ht ↦ (hHasDeriv t ht).hasDerivWithinAt)
        hMonotone (fun _ : ℝ ↦ (1 : ℝ))).1 hConstantIntegrable
    simpa only [smul_eq_mul, mul_one] using h
  simpa only [f, Real.norm_eq_abs] using hDerivativeIntegrable.norm

/-- A strict coefficient gap bounds scalar variance by the mean-scalar
derivative.  The coefficient is finite precisely because `κ < 6`.

This is the algebraic core of the finite-dissipation reduction.  Forward
volume constancy is derived from the normalized-flow equation and the moving
volume identity rather than assumed separately. -/
theorem normalizedFlowScalarVarianceTrack_le_coerciveGapFactor_mul_meanScalar_deriv_at
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
    {kappa : ℝ} (hkappa_lt : kappa < 6)
    (t : Ici (0 : ℝ))
    (hGap :
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    normalizedFlowScalarVarianceTrack gt t.1 ≤
      (3 * kappa * totalVolume (gt 0) / (6 - kappa)) *
        deriv (fun s ↦ meanScalar (gt s)) t.1 := by
  let variance : ℝ := normalizedFlowScalarVarianceTrack gt t.1
  let energy : ℝ := normalizedFlowTracelessRicciEnergyTrack gt t.1
  let volume0 : ℝ := totalVolume (gt 0)
  let meanDerivative : ℝ := deriv (fun s ↦ meanScalar (gt s)) t.1
  have hDenomPos : 0 < 6 - kappa := sub_pos.mpr hkappa_lt
  have hVolume0Pos : 0 < volume0 := by
    dsimp only [volume0]
    exact totalVolume_pos (gt 0)
  have hVolumeConstant : totalVolume (gt t.1) = volume0 := by
    dsimp only [volume0]
    exact totalVolume_eq_of_closedNormalizedRicciFlow_Ici
      (s := t.1) (t := 0)
      (fun r hr ↦ hFlow ⟨r, hr⟩)
      (fun r hr ↦ hDifferentiateMovingVolume ⟨r, hr⟩)
      t.2 (by norm_num)
  have hDerivative :
      meanDerivative = (2 * energy - (1 / 3 : ℝ) * variance) / volume0 := by
    have h :=
      (hasDerivAt_meanScalar_three_of_normalizedFlow
        (hFlow t) (hDifferentiateMovingTotalScalar t)
          (hDifferentiateMovingVolume t)).deriv
    dsimp only [meanDerivative, energy, variance]
    simpa only [normalizedFlowTracelessRicciEnergyTrack,
      normalizedFlowScalarVarianceTrack, hVolumeConstant] using h
  have hGap' : variance ≤ kappa * energy := by
    simpa only [variance, energy] using hGap
  have hScaled : variance * (6 - kappa) ≤
      3 * kappa * (2 * energy - (1 / 3 : ℝ) * variance) := by
    nlinarith [hGap']
  have hBeforeDerivative :
      variance ≤
        (3 * kappa * (2 * energy - (1 / 3 : ℝ) * variance)) /
          (6 - kappa) :=
    (le_div_iff₀ hDenomPos).2 <| by
      simpa only [mul_comm variance] using hScaled
  calc
    normalizedFlowScalarVarianceTrack gt t.1 ≤
        (3 * kappa * (2 * energy - (1 / 3 : ℝ) * variance)) /
          (6 - kappa) := hBeforeDerivative
    _ = (3 * kappa * totalVolume (gt 0) / (6 - kappa)) *
          deriv (fun s ↦ meanScalar (gt s)) t.1 := by
      rw [show deriv (fun s ↦ meanScalar (gt s)) t.1 = meanDerivative by rfl,
        hDerivative]
      dsimp only [volume0]
      ring_nf
      field_simp [totalVolume_ne_zero (gt 0)]

/-- Uniform forward-ray form of the pointwise coercive-gap estimate. -/
theorem normalizedFlowScalarVarianceTrack_le_coerciveGapFactor_mul_meanScalar_deriv
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
    {kappa : ℝ} (hkappa_lt : kappa < 6)
    (hGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        (3 * kappa * totalVolume (gt 0) / (6 - kappa)) *
          deriv (fun s ↦ meanScalar (gt s)) t.1 := by
  intro t
  exact
    normalizedFlowScalarVarianceTrack_le_coerciveGapFactor_mul_meanScalar_deriv_at
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hkappa_lt t (hGap t)

/-- Strict scalar-variance/traceless-energy domination produces finite
absolute dissipation from bounded nonnegative mean-scalar variation.

The only regularity premise not forced by one-dimensional calculus is
measurability of the scalar-variance track.  It is deliberately stated as
measurability, not as any form of the desired time integrability. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_coerciveGap
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
    {C kappa : ℝ}
    (hDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici (0 : ℝ), meanScalar (gt t.1) ≤ C)
    (hVarianceMeasurable : AEStronglyMeasurable
      (normalizedFlowScalarVarianceTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    (hkappa_nonneg : 0 ≤ kappa) (hkappa_lt : kappa < 6)
    (hGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (Ici 0) := by
  have hAbsoluteDerivative : IntegrableOn
      (fun t : ℝ ↦ |deriv (fun s ↦ meanScalar (gt s)) t|)
      (Ici 0) :=
    integrableOn_abs_deriv_meanScalar_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hDerivativeNonneg hMeanUpper
  let factor : ℝ :=
    3 * kappa * totalVolume (gt 0) / (6 - kappa)
  have hFactorNonneg : 0 ≤ factor := by
    dsimp only [factor]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hkappa_nonneg)
        (totalVolume_pos (gt 0)).le)
      (sub_nonneg.mpr hkappa_lt.le)
  have hMajorant : IntegrableOn
      (fun t : ℝ ↦ factor *
        |deriv (fun s ↦ meanScalar (gt s)) t|) (Ici 0) :=
    hAbsoluteDerivative.const_mul factor
  have hVarianceIntegrable :
      IntegrableOn (normalizedFlowScalarVarianceTrack gt) (Ici 0) := by
    apply hMajorant.mono' hVarianceMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have hVarianceNonneg :
        0 ≤ normalizedFlowScalarVarianceTrack gt t :=
      centeredScalarSqIntegral_nonneg (gt t)
    have hCoercive :=
      normalizedFlowScalarVarianceTrack_le_coerciveGapFactor_mul_meanScalar_deriv
        gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
          hkappa_lt hGap ⟨t, ht⟩
    have hDerivativeAtNonneg := hDerivativeNonneg ⟨t, ht⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hVarianceNonneg]
    simpa only [factor, abs_of_nonneg hDerivativeAtNonneg] using hCoercive
  simpa only [normalizedMeanScalarAbsoluteVarianceDissipation,
    normalizedFlowScalarVarianceTrack] using
      hAbsoluteDerivative.add hVarianceIntegrable

/-- The strict gap itself makes the mean-scalar derivative nonnegative, so
the derivative-sign premise of the preceding theorem is redundant.

Indeed `κ < 6` and nonnegativity of the traceless energy strengthen the gap
to `V ≤ 6 * E`; the exact normalized-flow identity then gives `mean' ≥ 0`.
This is the strongest direct finite-dissipation constructor in this file. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_coerciveGap_autoDerivNonneg
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
    {C kappa : ℝ}
    (hMeanUpper : ∀ t : Ici (0 : ℝ), meanScalar (gt t.1) ≤ C)
    (hVarianceMeasurable : AEStronglyMeasurable
      (normalizedFlowScalarVarianceTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    (hkappa_nonneg : 0 ≤ kappa) (hkappa_lt : kappa < 6)
    (hGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (Ici 0) := by
  have hSixGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1 := by
    intro t
    have hEnergyNonneg :
        0 ≤ normalizedFlowTracelessRicciEnergyTrack gt t.1 := by
      exact integral_nonneg fun x ↦
        (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
    exact (hGap t).trans <|
      mul_le_mul_of_nonneg_right hkappa_lt.le hEnergyNonneg
  have hDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1 :=
    meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hSixGap
  exact
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_coerciveGap
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hDerivativeNonneg hMeanUpper hVarianceMeasurable hkappa_nonneg
      hkappa_lt hGap

/-- An eventual strict gap is sufficient: bounded variation is proved
directly on `Ici T`, and continuity integrates the omitted compact interval.

Neither the gap nor derivative nonnegativity is required before `T`.  In
particular, no artificial global extension of the eventual Hamilton
coefficient is hidden in this theorem. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_eventual_coerciveGap
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
    {T C kappa : ℝ} (hT : 0 ≤ T)
    (hDissipationContinuous : ContinuousOn
      (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hMeanUpper : ∀ t : Ici (0 : ℝ), meanScalar (gt t.1) ≤ C)
    (hkappa_nonneg : 0 ≤ kappa) (hkappa_lt : kappa < 6)
    (hGap : ∀ t : Ici T,
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (Ici 0) := by
  have hFlowTail : ∀ t : Ici T, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x :=
    fun t x ↦ hFlow ⟨t.1, hT.trans t.2⟩ x
  have hTotalScalarTail : ∀ t : Ici T,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1 :=
    fun t ↦ hDifferentiateMovingTotalScalar ⟨t.1, hT.trans t.2⟩
  have hVolumeTail : ∀ t : Ici T,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1 :=
    fun t ↦ hDifferentiateMovingVolume ⟨t.1, hT.trans t.2⟩
  have hDerivativeNonnegTail : ∀ t : Ici T,
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1 := by
    intro t
    have hEnergyNonneg :
        0 ≤ normalizedFlowTracelessRicciEnergyTrack gt t.1 := by
      exact integral_nonneg fun x ↦
        (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
    have hSixGap :
        normalizedFlowScalarVarianceTrack gt t.1 ≤
          6 * normalizedFlowTracelessRicciEnergyTrack gt t.1 :=
      (hGap t).trans <|
        mul_le_mul_of_nonneg_right hkappa_lt.le hEnergyNonneg
    have hNumerator :
        0 ≤ 2 * normalizedFlowTracelessRicciEnergyTrack gt t.1 -
          (1 / 3 : ℝ) * normalizedFlowScalarVarianceTrack gt t.1 := by
      linarith
    have hDerivative :=
      (hasDerivAt_meanScalar_three_of_normalizedFlow
        (hFlowTail t) (hTotalScalarTail t) (hVolumeTail t)).deriv
    rw [hDerivative]
    apply div_nonneg
    · simpa only [normalizedFlowTracelessRicciEnergyTrack,
        normalizedFlowScalarVarianceTrack] using hNumerator
    · exact (totalVolume_pos (gt t.1)).le
  have hAbsoluteDerivativeTail : IntegrableOn
      (fun t : ℝ ↦ |deriv (fun s ↦ meanScalar (gt s)) t|)
      (Ici T) :=
    integrableOn_abs_deriv_meanScalar_of_normalizedFlow_Ici_start_of_deriv_nonneg_of_meanUpper
      gt hFlowTail hTotalScalarTail hVolumeTail hDerivativeNonnegTail
      (fun t ↦ hMeanUpper ⟨t.1, hT.trans t.2⟩)
  let factor : ℝ :=
    3 * kappa * totalVolume (gt 0) / (6 - kappa)
  have hFactorNonneg : 0 ≤ factor := by
    dsimp only [factor]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hkappa_nonneg)
        (totalVolume_pos (gt 0)).le)
      (sub_nonneg.mpr hkappa_lt.le)
  have hMajorant : IntegrableOn
      (fun t : ℝ ↦ (1 + factor) *
        |deriv (fun s ↦ meanScalar (gt s)) t|) (Ici T) :=
    hAbsoluteDerivativeTail.const_mul (1 + factor)
  have hTail : IntegrableOn
      (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici T) := by
    have hTailMeasurable : AEStronglyMeasurable
        (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (MeasureTheory.volume.restrict (Ici T)) :=
      (hDissipationContinuous.mono (Ici_subset_Ici.2 hT))
        |>.aestronglyMeasurable measurableSet_Ici
    apply hMajorant.mono' hTailMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : t ∈ Ici (0 : ℝ) := hT.trans ht
    have hDerivativeAtNonneg := hDerivativeNonnegTail ⟨t, ht⟩
    have hCoercive :=
      normalizedFlowScalarVarianceTrack_le_coerciveGapFactor_mul_meanScalar_deriv_at
        gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hkappa_lt ⟨t, ht0⟩ (hGap ⟨t, ht⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (normalizedMeanScalarAbsoluteVarianceDissipation_nonneg gt t)]
    change
      |deriv (fun s ↦ meanScalar (gt s)) t| +
          normalizedFlowScalarVarianceTrack gt t ≤
        (1 + factor) * |deriv (fun s ↦ meanScalar (gt s)) t|
    rw [abs_of_nonneg hDerivativeAtNonneg]
    dsimp only [factor]
    nlinarith
  exact integrableOn_Ici_zero_of_continuousOn_of_integrableOn_tail
    hT hDissipationContinuous hTail

/-- Compact joint scalar continuity automatically supplies the finite mean
upper bound needed by the coercive-gap theorem. -/
theorem exists_pos_meanScalarUpper_of_compact_parameterization_of_joint_scalar
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : Ici (0 : ℝ),
      meanScalar (gt t.1) ≤ C := by
  obtain ⟨C, hC, hScalarBound⟩ :=
    exists_pos_uniform_abs_scalarAt_bound_of_compact_joint_scalar
      metric hJointScalar
  refine ⟨C, hC, ?_⟩
  intro t
  have hMean : meanScalar (metric (parameter t)) ≤ C :=
    meanScalar_le_of_forall_scalarAt_le (metric (parameter t)) C
      fun x ↦ (le_abs_self _).trans (hScalarBound (parameter t) x)
  simpa only [hRealizes t] using hMean

/-- Compact-family form of the automatic coercive-gap constructor.  It
removes an explicit mean-upper-bound field from downstream analytic packages;
joint scalar continuity on `K × M` constructs that bound internally. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_coerciveGap
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hVarianceMeasurable : AEStronglyMeasurable
      (normalizedFlowScalarVarianceTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {kappa : ℝ} (hkappa_nonneg : 0 ≤ kappa) (hkappa_lt : kappa < 6)
    (hGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x)) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (Ici 0) := by
  obtain ⟨C, _hC, hMeanUpper⟩ :=
    exists_pos_meanScalarUpper_of_compact_parameterization_of_joint_scalar
      gt metric parameter hRealizes hJointScalar
  exact
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_coerciveGap_autoDerivNonneg
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hMeanUpper hVarianceMeasurable hkappa_nonneg hkappa_lt hGap

/-- Fully geometric compact-family variant.  A continuous parameterization,
weak continuity of the moving finite-volume measure, and joint scalar
continuity construct scalar-variance measurability automatically. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_continuity_coerciveGap
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
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
    {kappa : ℝ} (hkappa_nonneg : 0 ≤ kappa) (hkappa_lt : kappa < 6)
    (hGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x)) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (Ici 0) := by
  have hVarianceMeasurable : AEStronglyMeasurable
      (normalizedFlowScalarVarianceTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)) :=
    normalizedFlowScalarVarianceTrack_aestronglyMeasurable_of_compact_parameterization
      gt metric parameter hParameter hRealizes hMeasure hJointScalar
  exact
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_coerciveGap
      gt metric parameter hRealizes hFlow hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hVarianceMeasurable hkappa_nonneg
      hkappa_lt hGap hJointScalar

namespace NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3

/-- Record constructor for the compact finite-time positive-Einstein package
with its former finite-dissipation input replaced by the strict coercive gap
and scalar-variance measurability.

The compact joint scalar field supplies the mean upper bound, while the gap
supplies both derivative nonnegativity and variance integrability.  Thus the
constructed record's `finiteAbsoluteDissipation` field is a theorem, not an
input. -/
def ofCoerciveGap
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (realizesFlow : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (compactTensorReferenceControl :
      CompactReferenceMetricTensorFamilyData K metric)
    (fullCovariantRicciDerivativeBound meanScalarFloor : ℝ)
    (covariantDerivativeRegularity : ∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt t.1).leviCivita 1)
    (meanScalarFloor_pos : 0 < meanScalarFloor)
    (normalizedFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (jointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t.1 x 3)
    (differentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (differentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (scalarVarianceMeasurable : AEStronglyMeasurable
      (normalizedFlowScalarVarianceTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {kappa : ℝ} (kappa_nonneg : 0 ≤ kappa) (kappa_lt : kappa < 6)
    (scalarVarianceEnergyGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1)
    (fullCovariantRicciControl :
      UniformCovariantRicciDerivativeNormBound
        (fun t : Ici (0 : ℝ) ↦ gt t.1)
          fullCovariantRicciDerivativeBound)
    (meanScalarLower : ∀ t : Ici (0 : ℝ),
      meanScalarFloor ≤ meanScalar (gt t.1))
    (scalarJointContinuous : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (tracelessRicciNormSqJointContinuous : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
      M := by
  letI : Nonempty K := ⟨parameter ⟨0, by simp⟩⟩
  exact {
    K := K
    topologicalSpaceK := inferInstance
    compactSpaceK := inferInstance
    gt := gt
    metric := metric
    parameter := parameter
    realizesFlow := realizesFlow
    compactTensorReferenceControl := compactTensorReferenceControl
    fullCovariantRicciDerivativeBound := fullCovariantRicciDerivativeBound
    meanScalarFloor := meanScalarFloor
    covariantDerivativeRegularity := covariantDerivativeRegularity
    meanScalarFloor_pos := meanScalarFloor_pos
    normalizedFlow := normalizedFlow
    jointMetricEntries := jointMetricEntries
    differentiateMovingTotalScalar := differentiateMovingTotalScalar
    differentiateMovingVolume := differentiateMovingVolume
    finiteAbsoluteDissipation :=
      normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_coerciveGap
        gt metric parameter realizesFlow normalizedFlow
        differentiateMovingTotalScalar differentiateMovingVolume
        scalarVarianceMeasurable kappa_nonneg kappa_lt
        scalarVarianceEnergyGap scalarJointContinuous
    fullCovariantRicciControl := fullCovariantRicciControl
    meanScalarLower := meanScalarLower
    scalarJointContinuous := scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      tracelessRicciNormSqJointContinuous }

/-- Geometric-continuity constructor for the same compact analytic package.
Compared with `ofCoerciveGap`, it replaces raw scalar-variance measurability
by a continuous parameter, weak continuity of the moving Riemannian volume
measure, and the already-required joint scalar continuity. -/
def ofCoerciveGapOfCompactContinuity
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (parameterContinuous : Continuous parameter)
    (realizesFlow : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (compactTensorReferenceControl :
      CompactReferenceMetricTensorFamilyData K metric)
    (fullCovariantRicciDerivativeBound meanScalarFloor : ℝ)
    (covariantDerivativeRegularity : ∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt t.1).leviCivita 1)
    (meanScalarFloor_pos : 0 < meanScalarFloor)
    (normalizedFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (jointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t.1 x 3)
    (differentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (differentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (finiteVolumeMeasureContinuous : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    {kappa : ℝ} (kappa_nonneg : 0 ≤ kappa) (kappa_lt : kappa < 6)
    (scalarVarianceEnergyGap : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1)
    (fullCovariantRicciControl :
      UniformCovariantRicciDerivativeNormBound
        (fun t : Ici (0 : ℝ) ↦ gt t.1)
          fullCovariantRicciDerivativeBound)
    (meanScalarLower : ∀ t : Ici (0 : ℝ),
      meanScalarFloor ≤ meanScalar (gt t.1))
    (scalarJointContinuous : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (tracelessRicciNormSqJointContinuous : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
      M := by
  letI : Nonempty K := ⟨parameter ⟨0, by simp⟩⟩
  apply ofCoerciveGap gt metric parameter realizesFlow
    compactTensorReferenceControl fullCovariantRicciDerivativeBound
    meanScalarFloor covariantDerivativeRegularity meanScalarFloor_pos
    normalizedFlow jointMetricEntries differentiateMovingTotalScalar
    differentiateMovingVolume
  · exact
      normalizedFlowScalarVarianceTrack_aestronglyMeasurable_of_compact_parameterization
        gt metric parameter parameterContinuous realizesFlow
        finiteVolumeMeasureContinuous scalarJointContinuous
  · exact kappa_nonneg
  · exact kappa_lt
  · exact scalarVarianceEnergyGap
  · exact fullCovariantRicciControl
  · exact meanScalarLower
  · exact scalarJointContinuous
  · exact tracelessRicciNormSqJointContinuous

end NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3

end Poincare
