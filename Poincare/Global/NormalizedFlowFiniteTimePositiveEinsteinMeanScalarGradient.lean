import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalar
import Poincare.Global.NormalizedFlowEnergyConcentrationLipschitzBridge
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity
import Poincare.Global.NormalizedFlowJointPinchingRegularity
import Poincare.Global.ScalarMeanLowerBound

/-!
# Mean-scalar Einstein endpoint from a scalar-gradient bound

This module removes the standalone scalar-variance Lipschitz premise from the
strongest compact tensor-reference-family mean-scalar endpoint.  A uniform
bound on the centered scalar and an intrinsic uniform spatial derivative
bound for scalar curvature imply the needed Lipschitz estimate for
`(R - meanScalar) ^ 2`.

The mean scalar is constant in the spatial variable on each time slice.  The
proof therefore differentiates only `R`; it does not introduce or assume a
spatial derivative of the mean.  The existing `|∇ Ric°|` bound remains
insufficient for this step because it does not control the trace derivative.
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

local notation "I" => closedSmoothModelWithCorners 3

/-- Joint scalar continuity on a compact metric family supplies one positive
uniform absolute scalar-curvature bound. -/
theorem exists_pos_uniform_abs_scalarAt_bound_of_compact_joint_scalar
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : K, ∀ x : M,
      |(metric k).scalarAt x| ≤ C := by
  have hAbsScalar : Continuous ↿(fun k (x : M) ↦
      |(metric k).scalarAt x|) := hJointScalar.abs
  obtain ⟨pMax, _hpMax, hpMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (K × M))).exists_isMaxOn
      Set.univ_nonempty hAbsScalar.continuousOn
  let C : ℝ := |(metric pMax.1).scalarAt pMax.2| + 1
  refine ⟨C, add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one, ?_⟩
  intro k x
  exact (hpMax (Set.mem_univ (k, x))).trans (le_add_of_nonneg_right zero_le_one)

/-- Joint scalar continuity on a compact family bounds every centered scalar
on that family.  The proof first bounds `|R|` by `C`, then uses that the mean
lies between the pointwise lower and upper scalar bounds to get
`|meanScalar| ≤ C`, hence `|R - meanScalar| ≤ 2 * C`. -/
theorem exists_pos_uniform_centeredScalar_bound_of_compact_joint_scalar
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : K, ∀ x : M,
      |(metric k).scalarAt x - meanScalar (metric k)| ≤ C := by
  obtain ⟨S, hS, hScalar⟩ :=
    exists_pos_uniform_abs_scalarAt_bound_of_compact_joint_scalar
      metric hJointScalar
  refine ⟨2 * S, mul_pos (by norm_num) hS, ?_⟩
  intro k x
  calc
    |(metric k).scalarAt x - meanScalar (metric k)|
        ≤ |(metric k).scalarAt x| + |meanScalar (metric k)| :=
      by simpa using
        (abs_sub_le ((metric k).scalarAt x) (0 : ℝ)
          (meanScalar (metric k)))
    _ ≤ S + S := add_le_add (hScalar k x)
      (abs_meanScalar_le_of_forall_abs_scalarAt_le
        (metric k) S (hScalar k))
    _ = 2 * S := by ring

/-- Joint continuity of squared traceless-Ricci norm on a compact metric
family supplies one positive uniform pointwise norm bound.

No sign hypothesis is needed: squared traceless-Ricci norm is intrinsically
nonnegative.  We maximize it on `K × M`, then enlarge that maximum by one so
the resulting constant is strictly positive and its square still dominates
the maximum. -/
theorem exists_pos_uniform_tracelessRicciNormSqAt_bound_of_compact_joint
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : K, ∀ x : M,
      (metric k).tracelessRicciNormSqAt x ≤ A ^ 2 := by
  obtain ⟨pMax, _hpMax, hpMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (K × M))).exists_isMaxOn
      Set.univ_nonempty hJointTraceless.continuousOn
  let S : ℝ := (metric pMax.1).tracelessRicciNormSqAt pMax.2
  have hSNonneg : 0 ≤ S := by
    dsimp only [S]
    exact
      (metric pMax.1).tracelessRicciNormSqAt_nonneg pMax.2 (by norm_num)
  let A : ℝ := S + 1
  have hApos : 0 < A := by
    dsimp only [A]
    exact add_pos_of_nonneg_of_pos hSNonneg zero_lt_one
  have hOneLeA : (1 : ℝ) ≤ A := by
    dsimp only [A]
    calc
      (1 : ℝ) = 1 + 0 := (add_zero 1).symm
      _ ≤ 1 + S := add_le_add_right hSNonneg 1
      _ = S + 1 := add_comm 1 S
  have hAleSq : A ≤ A ^ 2 := by
    calc
      A = A * 1 := (mul_one A).symm
      _ ≤ A * A := mul_le_mul_of_nonneg_left hOneLeA hApos.le
      _ = A ^ 2 := (pow_two A).symm
  have hSleSq : S ≤ A ^ 2 :=
    (le_add_of_nonneg_right zero_le_one : S ≤ S + 1).trans hAleSq
  refine ⟨A, hApos, ?_⟩
  intro k x
  have hle : (metric k).tracelessRicciNormSqAt x ≤ S := by
    simpa only [S] using hpMax (Set.mem_univ (k, x))
  exact hle.trans hSleSq

/-- Finite absolute dissipation, a bounded centered scalar, and an intrinsic
uniform scalar-gradient bound produce a positive Einstein limit under the
same compact tensor-reference and traceless-curvature hypotheses as the
previous strongest mean-scalar endpoint.

The derived scalar-variance Lipschitz constant is `2 * C * G`. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_centeredScalarBound_of_scalarGradientBound_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B C G c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hC : 0 < C)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hCenteredScalarBound : ∀ t : ℝ, ∀ x : M,
      |(gt t).scalarAt x - meanScalar (gt t)| ≤ C)
    (hScalarGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).scalarAt x) G)
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  have hScalarVarianceLipschitz :
      UniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2)
        (2 * C * G) :=
    uniformClosedRiemannianLipschitzBound_centeredScalarSq_of_centeredBound_of_scalarMFDerivBound
      gt hC hCenteredScalarBound hScalarGradient
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

/-- Compact joint scalar continuity automatically supplies the uniform
centered-scalar bound needed by the scalar-gradient endpoint. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_compactJointScalar_of_scalarGradientBound_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B G c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hScalarGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).scalarAt x) G)
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨C, hC, hCenteredMetric⟩ :=
    exists_pos_uniform_centeredScalar_bound_of_compact_joint_scalar
      metric hJointScalar
  have hCenteredFlow : ∀ t : ℝ, ∀ x : M,
      |(gt t).scalarAt x - meanScalar (gt t)| ≤ C := by
    intro t x
    simpa only [hRealize t] using hCenteredMetric (parameter t) x
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_centeredScalarBound_of_scalarGradientBound_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
      gt metric parameter hRealize compactControl hc hC hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCenteredFlow hScalarGradient hCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

/-- Joint scalar and exponent-zero pinching continuity on the compact family
remove both the centered-scalar bound and the opaque invariant-pair
continuity premise from the scalar-gradient mean-scalar endpoint. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_compactJointScalar_of_scalarGradientBound_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_pinching
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B G c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hScalarGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).scalarAt x) G)
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointPinching : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0)) :
    PositiveEinsteinMetric3 M := by
  have hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)) :=
    continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_joint
      metric hJointScalar hJointPinching
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_compactJointScalar_of_scalarGradientBound_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarGradient hCOne hBounds hMeanLower
      hForwardScalarPos hTQTwo hJointScalar hInvariantContinuous

/-- Full covariant-Ricci derivative control supplies both the scalar-gradient
bound and the traceless covariant-Ricci derivative bound.  With compact joint
scalar and pinching continuity, the resulting endpoint has no separate
scalar-gradient, centered-scalar, scalar-variance Lipschitz, or invariant-pair
continuity premise. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_pinching
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A D c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hScalarCOne : UniformScalarCurvatureCOne gt)
    (hTracelessCOne : UniformTracelessRicciEnergyCOne gt)
    (hTracelessRicci : UniformTracelessRicciNormBound gt A)
    (hFullCovariantRicci :
      UniformCovariantRicciDerivativeNormBound gt D)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointPinching : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0)) :
    PositiveEinsteinMetric3 M := by
  have hScalarGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).scalarAt x) (3 * D) :=
    uniformClosedRiemannianMFDerivBound_scalarAt_of_covariantRicciDerivativeNormBound
      gt hScalarCOne hFullCovariantRicci
  have hBounds :
      UniformTracelessRicciAndCovariantDerivativeNormBound gt A D :=
    uniformTracelessRicciAndCovariantDerivativeNormBound_of_tracelessRicci_of_covariantRicciDerivative
      gt hTracelessRicci hFullCovariantRicci
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_compactJointScalar_of_scalarGradientBound_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_pinching
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarGradient hTracelessCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hJointScalar hJointPinching

/-- Global joint `C³` metric-entry regularity derives the spatial `C¹` scalar
and traceless-Ricci-energy regularity used by the denominator-free compact
energy-pair endpoint.  Joint squared-traceless-Ricci continuity on the compact
reference family also constructs, rather than assumes, the uniform pointwise
traceless-Ricci bound.

Because the compact limit tracks the absolute traceless-Ricci maximum, this
theorem needs no forward scalar-positivity, pinching-quotient regularity, or
compact-family pinching-continuity premise. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {D c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJointMetricEntries : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hFullCovariantRicci :
      UniformCovariantRicciDerivativeNormBound gt D)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨A, hA, hTracelessMetric⟩ :=
    exists_pos_uniform_tracelessRicciNormSqAt_bound_of_compact_joint
      metric hJointTraceless
  have hTracelessRicci : UniformTracelessRicciNormBound gt A := by
    refine ⟨hA, ?_⟩
    intro t x
    simpa only [hRealize t] using hTracelessMetric (parameter t) x
  obtain ⟨C, hC, hCenteredMetric⟩ :=
    exists_pos_uniform_centeredScalar_bound_of_compact_joint_scalar
      metric hJointScalar
  have hCenteredFlow : ∀ t : ℝ, ∀ x : M,
      |(gt t).scalarAt x - meanScalar (gt t)| ≤ C := by
    intro t x
    simpa only [hRealize t] using hCenteredMetric (parameter t) x
  have hScalarCOne : UniformScalarCurvatureCOne gt := by
    intro t x
    exact
      (scalarAt_contMDiffAt_two_of_normalizedRicciFlow
        (hFlow t)
        (fun y ↦
          timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
            (hJointMetricEntries t y)) x).of_le (by norm_num)
  have hTracelessCOne : UniformTracelessRicciEnergyCOne gt :=
    contMDiff_one_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three
      hFlow hJointMetricEntries
  have hScalarGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).scalarAt x) (3 * D) :=
    uniformClosedRiemannianMFDerivBound_scalarAt_of_covariantRicciDerivativeNormBound
      gt hScalarCOne hFullCovariantRicci
  have hScalarVarianceLipschitz :
      UniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2)
        (2 * C * (3 * D)) :=
    uniformClosedRiemannianLipschitzBound_centeredScalarSq_of_centeredBound_of_scalarMFDerivBound
      gt hC hCenteredFlow hScalarGradient
  have hBounds :
      UniformTracelessRicciAndCovariantDerivativeNormBound gt A D :=
    uniformTracelessRicciAndCovariantDerivativeNormBound_of_tracelessRicci_of_covariantRicciDerivative
      gt hTracelessRicci hFullCovariantRicci
  have hTracelessLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * D) :=
    uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      gt hTracelessCOne hBounds
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes parameter gt hRealize
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization
      gt metric parameter hRealize hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hNoncollapse hMeanLower hJointScalar hJointTraceless

/-- Compatibility spelling for the former quotient-based strongest endpoint.
The forward-positivity and pinching-continuity inputs are no longer consumed;
the conclusion follows through the denominator-free absolute-energy pair. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_pinching_of_jointMetricEntriesThree
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {D c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJointMetricEntries : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hFullCovariantRicci :
      UniformCovariantRicciDerivativeNormBound gt D)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (_hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x))
    (_hJointPinching : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0)) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    gt metric parameter hRealize compactControl hc hFlow
    hJointMetricEntries hDifferentiateMovingTotalScalar
    hDifferentiateMovingVolume hFiniteDissipation hFullCovariantRicci
    hMeanLower hJointScalar hJointTraceless

end Poincare
