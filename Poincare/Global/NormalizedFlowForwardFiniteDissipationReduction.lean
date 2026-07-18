import Poincare.Global.NormalizedFlowForwardAbsoluteDissipation
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Forward finite-dissipation reduction

For a forward normalized Ricci flow, nonnegativity of the mean-scalar
derivative and a finite upper bound for the mean scalar already make the
absolute derivative integrable on `Ici 0`.  This is a one-dimensional
bounded-variation fact: the mean scalar is monotone, and its forward image is
contained in a bounded interval.

The same assumptions do not by themselves make the scalar variance
integrable.  This module records the exact remaining boundary.  Finite
absolute dissipation is equivalent to time-integrability of the scalar
variance.  Using the three-dimensional mean-scalar identity and forward
volume constancy, it is also equivalent to time-integrability of the total
squared traceless-Ricci curvature.

Every flow, differentiation, sign, and upper-bound hypothesis is indexed by
the proof-carrying subtype `Ici 0`; no negative-time regularity is used.
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

/-- Scalar-curvature variance along a metric path. -/
noncomputable def normalizedFlowScalarVarianceTrack
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) : ℝ :=
  ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
    ∂(volumeMeasure (gt t))

/-- Total squared traceless-Ricci curvature along a metric path. -/
noncomputable def normalizedFlowTracelessRicciEnergyTrack
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) : ℝ :=
  ∫ x, (gt t).tracelessRicciNormSqAt x ∂(volumeMeasure (gt t))

omit [SecondCountableTopology M] in
/-- A nonnegative mean-scalar derivative and a concrete forward upper bound
make the absolute mean-scalar derivative integrable on `Ici 0`.

The proof first obtains forward monotonicity from the derivative sign.  The
change-of-variables integrability theorem is then applied to the bounded
image of the mean-scalar track. -/
theorem integrableOn_abs_deriv_meanScalar_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
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
    {C : ℝ}
    (hDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici (0 : ℝ),
      meanScalar (gt t.1) ≤ C) :
    IntegrableOn
      (fun t : ℝ ↦ |deriv (fun s ↦ meanScalar (gt s)) t|)
      (Ici 0) := by
  let f : ℝ → ℝ := fun t ↦ meanScalar (gt t)
  have hHasDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt f (deriv f t) t := by
    intro t ht
    simpa only [f] using
      (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
        (hFlow ⟨t, ht⟩) (by norm_num)
        (hDifferentiateMovingTotalScalar ⟨t, ht⟩)
        (hDifferentiateMovingVolume ⟨t, ht⟩)).differentiableAt.hasDerivAt
  have hContinuous : ContinuousOn f (Ici (0 : ℝ)) := by
    intro t ht
    exact (hHasDeriv t ht).continuousAt.continuousWithinAt
  have hDifferentiable : DifferentiableOn ℝ f (interior (Ici (0 : ℝ))) := by
    intro t ht
    exact
      (hHasDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hDerivativeNonneg' : ∀ t ∈ interior (Ici (0 : ℝ)),
      0 ≤ deriv f t := by
    intro t ht
    simpa only [f] using hDerivativeNonneg ⟨t, interior_subset ht⟩
  have hMonotone : MonotoneOn f (Ici (0 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hContinuous
      hDifferentiable hDerivativeNonneg'
  have hImageSubset : f '' Ici (0 : ℝ) ⊆ Icc (f 0) C := by
    rintro y ⟨t, ht, rfl⟩
    constructor
    · exact hMonotone (by norm_num) ht ht
    · simpa only [f] using hMeanUpper ⟨t, ht⟩
  have hConstantIntegrable : IntegrableOn
      (fun _ : ℝ ↦ (1 : ℝ)) (f '' Ici (0 : ℝ)) :=
    (integrableOn_const measure_Icc_lt_top.ne).mono_set hImageSubset
  have hDerivativeIntegrable : IntegrableOn (deriv f) (Ici 0) := by
    have h :=
      (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        measurableSet_Ici
        (fun t ht ↦ (hHasDeriv t ht).hasDerivWithinAt)
        hMonotone (fun _ : ℝ ↦ (1 : ℝ))).1 hConstantIntegrable
    simpa only [smul_eq_mul, mul_one] using h
  simpa only [f, Real.norm_eq_abs] using hDerivativeIntegrable.norm

omit [SecondCountableTopology M] in
/-- Once the absolute mean-scalar derivative is integrable, finite absolute
dissipation is exactly time-integrability of the scalar variance. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_iff_scalarVarianceTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
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
    {C : ℝ}
    (hDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici (0 : ℝ),
      meanScalar (gt t.1) ≤ C) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) ↔
      IntegrableOn (normalizedFlowScalarVarianceTrack gt) (Ici 0) := by
  have hAbsoluteDerivative : IntegrableOn
      (fun t : ℝ ↦ |deriv (fun s ↦ meanScalar (gt s)) t|)
      (Ici 0) :=
    integrableOn_abs_deriv_meanScalar_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hDerivativeNonneg hMeanUpper
  constructor
  · intro hDissipation
    have hDifference := hDissipation.sub hAbsoluteDerivative
    refine hDifference.congr_fun ?_ measurableSet_Ici
    intro t _ht
    simp only [Pi.sub_apply,
      normalizedMeanScalarAbsoluteVarianceDissipation,
      normalizedFlowScalarVarianceTrack, add_sub_cancel_left]
  · intro hVariance
    simpa only [normalizedMeanScalarAbsoluteVarianceDissipation,
      normalizedFlowScalarVarianceTrack] using
      hAbsoluteDerivative.add hVariance

/-- Under the exact three-dimensional normalized-flow identity and forward
volume constancy, time-integrability of scalar variance is equivalent to
time-integrability of total squared traceless-Ricci curvature. -/
theorem normalizedFlowScalarVarianceTrack_integrableOn_iff_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
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
    {C : ℝ}
    (hDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici (0 : ℝ),
      meanScalar (gt t.1) ≤ C) :
    IntegrableOn (normalizedFlowScalarVarianceTrack gt) (Ici 0) ↔
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  let f : ℝ → ℝ := fun t ↦ meanScalar (gt t)
  have hAbsoluteDerivative : IntegrableOn (fun t : ℝ ↦ |deriv f t|)
      (Ici 0) := by
    simpa only [f] using
      integrableOn_abs_deriv_meanScalar_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
        gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hDerivativeNonneg hMeanUpper
  have hDerivativeIntegrable : IntegrableOn (deriv f) (Ici 0) := by
    refine hAbsoluteDerivative.congr_fun ?_ measurableSet_Ici
    intro t ht
    change |deriv f t| = deriv f t
    exact abs_of_nonneg <| by
      simpa only [f] using hDerivativeNonneg ⟨t, ht⟩
  have hDerivativeEnergy : ∀ t ∈ Ici (0 : ℝ),
      deriv f t =
        normalizedMeanScalarEnergyNumerator (gt t) / totalVolume (gt t) := by
    intro t ht
    simpa only [f] using
      (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
        (hFlow ⟨t, ht⟩) (by norm_num)
        (hDifferentiateMovingTotalScalar ⟨t, ht⟩)
        (hDifferentiateMovingVolume ⟨t, ht⟩)).deriv
  have hVolumeConstant : ∀ t ∈ Ici (0 : ℝ),
      totalVolume (gt t) = totalVolume (gt 0) := by
    intro t ht
    exact totalVolume_eq_of_closedNormalizedRicciFlow_Ici
      (s := t) (t := 0)
      (fun r hr ↦ hFlow ⟨r, hr⟩)
      (fun r hr ↦ hDifferentiateMovingVolume ⟨r, hr⟩)
      ht (by norm_num)
  have hEnergyEq : EqOn (normalizedFlowTracelessRicciEnergyTrack gt)
      (fun t ↦
        (totalVolume (gt 0) / 2) * deriv f t +
          (1 / 6 : ℝ) * normalizedFlowScalarVarianceTrack gt t)
      (Ici (0 : ℝ)) := by
    intro t ht
    have hNumerator : normalizedMeanScalarEnergyNumerator (gt t) =
        deriv f t * totalVolume (gt t) := by
      calc
        normalizedMeanScalarEnergyNumerator (gt t) =
            (normalizedMeanScalarEnergyNumerator (gt t) /
              totalVolume (gt t)) * totalVolume (gt t) :=
          (div_mul_cancel₀ _ (totalVolume_ne_zero (gt t))).symm
        _ = deriv f t * totalVolume (gt t) := by
          rw [← hDerivativeEnergy t ht]
    rw [normalizedMeanScalarEnergyNumerator_three,
      hVolumeConstant t ht] at hNumerator
    change
      2 * normalizedFlowTracelessRicciEnergyTrack gt t -
          (1 / 3 : ℝ) * normalizedFlowScalarVarianceTrack gt t =
        deriv f t * totalVolume (gt 0) at hNumerator
    linarith
  have hVarianceEq : EqOn (normalizedFlowScalarVarianceTrack gt)
      (fun t ↦
        6 * normalizedFlowTracelessRicciEnergyTrack gt t -
          (3 * totalVolume (gt 0)) * deriv f t)
      (Ici (0 : ℝ)) := by
    intro t ht
    have h := hEnergyEq ht
    linarith
  constructor
  · intro hVariance
    have hRight : IntegrableOn
        (fun t ↦
          (totalVolume (gt 0) / 2) * deriv f t +
            (1 / 6 : ℝ) * normalizedFlowScalarVarianceTrack gt t)
        (Ici 0) :=
      (hDerivativeIntegrable.const_mul (totalVolume (gt 0) / 2)).add
        (hVariance.const_mul (1 / 6 : ℝ))
    exact hRight.congr_fun (fun t ht ↦ (hEnergyEq ht).symm)
      measurableSet_Ici
  · intro hEnergy
    have hRight : IntegrableOn
        (fun t ↦
          6 * normalizedFlowTracelessRicciEnergyTrack gt t -
            (3 * totalVolume (gt 0)) * deriv f t)
        (Ici 0) :=
      (hEnergy.const_mul 6).sub
        (hDerivativeIntegrable.const_mul (3 * totalVolume (gt 0)))
    exact hRight.congr_fun (fun t ht ↦ (hVarianceEq ht).symm)
      measurableSet_Ici

/-- Combined reduction: under forward mean-scalar monotonicity data and a
finite upper bound, finite absolute dissipation is exactly finite
time-integrated total traceless-Ricci energy. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_iff_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
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
    {C : ℝ}
    (hDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici (0 : ℝ),
      meanScalar (gt t.1) ≤ C) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) ↔
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) :=
  (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_iff_scalarVarianceTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
    gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hDerivativeNonneg hMeanUpper).trans
    (normalizedFlowScalarVarianceTrack_integrableOn_iff_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hDerivativeNonneg hMeanUpper)

/-- Producer form of the combined reduction, ready to discharge the finite
absolute-dissipation premise of forward geometric endpoints. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
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
    {C : ℝ}
    (hDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici (0 : ℝ),
      meanScalar (gt t.1) ≤ C)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0)) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) :=
  (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_iff_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
    gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hDerivativeNonneg hMeanUpper).2 hFiniteTracelessRicciEnergy

end Poincare
