import Poincare.Global.NormalizedFlowFiniteTimeCurvatureCompactness
import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.EinsteinNormalization

/-!
# A finite normalized-flow slice produces a positive Einstein limit

This file closes the analytic chain assembled by the finite-time
concentration and Hamilton-pinching modules.

Finite absolute dissipation, intrinsic curvature-derivative control, and a
compact reference family first select a time with an `R / 4` Ricci
eigenvalue floor.  Ordinary Hamilton quotient evolution then transports that
single floor to an `R / 6` floor at every later time.  The improved quotient
evolution makes the relative-pinching maximum antitone, while finite
dissipation supplies an escaping uniformly round subsequence; together they
force full forward relative-traceless-Ricci decay.  Compactness of only the
integer-time scalar-minimum/relative-pinching pair range then realizes a
positive Einstein metric.

In particular, neither the finite slice nor the forward `R / 6` floor is an
assumption of the strongest end-to-end theorem, and no separate integrability
of the pinching maximum or continuity of a compact metric orbit is required.
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

/-- An initial `R / 4` eigenvalue floor and ordinary Hamilton quotient
evolution on the whole forward ray generate the `R / 6` floor required by
the improved pinching maximum principle at every forward time. -/
theorem globalRicciEigenvalueFloor_one_sixth_forward_of_global_one_fourth_initial_floor
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hInitFloor : GlobalRicciEigenvalueFloor3 (gt t0) (1 / 4))
    (hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x)
    (hQCont :
      Continuous ↿(fun s (x : M) ↦
        (gt (t0 + s)).pinchingQuotientAt x))
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t0 + s) x
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x)) :
    ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) (1 / 6) := by
  intro s hs
  have hTransport :=
    hamilton_eigenvalue_pinching_floor_preserved
      (gt := gt) (t₀ := t0) (T := s) (ε := (1 / 4 : ℝ))
      rfl (by norm_num) hs hQCont
      (fun tau htau x ↦ hQTwo tau htau.1 x)
      (fun tau htau x ↦ hQEvol tau htau.1 x)
      (fun tau htau x ↦ hRpos tau htau.1 x)
      hInitFloor
  intro x b mu hEig i
  have hi := hTransport s ⟨hs, le_rfl⟩ x b mu hEig i
  norm_num at hi ⊢
  exact hi

/-- A fixed `R / 4` slice reaches a positive Einstein metric when the
integer-time range of the two limit invariants is compact.

This is the range-only Hamilton endpoint: it does not assume a compact space
of metrics, continuity of the invariant map on such a space, or convergence
of the metric orbit.  Every point of the compact range is automatically
realized by the corresponding integer-time flow metric. -/
theorem positiveEinsteinMetric3_of_global_one_fourth_initial_floor_of_hamilton_improvement_of_integrableMaximum_of_compact_integer_invariant_pair_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hInitFloor : GlobalRicciEigenvalueFloor3 (gt t0) (1 / 4))
    (hc : 0 < c)
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt (t0 + s)).scalarAt x)
    (hQCont :
      Continuous ↿(fun s (x : M) ↦
        (gt (t0 + s)).pinchingQuotientAt x))
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t0 + s) x
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ s ∈ Ici (0 : ℝ),
      Continuous ↿(fun tau (x : M) ↦
        (gt ((t0 + s) + tau)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + s) x 0
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hIntegrable :
      IntegrableOn (tracelessPinchingMaximumTrack gt t0 0) (Ici 0))
    (hInvariantPairRangeCompact : IsCompact
      (Set.range fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + (i : ℝ))))) :
    PositiveEinsteinMetric3 M := by
  have hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x :=
    fun s hs x ↦ hc.trans_le (hScalarLower s hs x)
  have hForwardFloor : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) (1 / 6) :=
    globalRicciEigenvalueFloor_one_sixth_forward_of_global_one_fourth_initial_floor
      gt hInitFloor hRpos hQCont hQTwo hQEvol
  have hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 0) (Ici (0 : ℝ)) :=
    tracelessPinchingMaximumTrack_antitoneOn_of_hamilton_forward_improvement
      (gt := gt) (t0 := t0) (epsilon := (1 / 6 : ℝ)) (delta := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [PinchingAlgebra.pinchedTracelessAdmissibleDelta3])
      hTQCont hTQTwo hTQEvol hForwardFloor
  have hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) :=
    tracelessPinchingMaximumTrack_tendsto_zero_of_antitoneOn_of_integrableOn
      gt hRpos hTQTwo hAntitone hIntegrable
  let C : Set (ℝ × ℝ) := Set.range fun i : ℕ ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair
      (gt (t0 + (i : ℝ)))
  apply positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core
  apply
    hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
      gt hc hMaximumZero hScalarLower C
  · simpa only [C] using hInvariantPairRangeCompact
  · intro i
    exact ⟨i, rfl⟩
  · rintro p ⟨i, rfl⟩
    exact ⟨gt (t0 + (i : ℝ)), rfl⟩

/-- End-to-end finite-time Hamilton compact-limit consumer.

The compact reference data are used twice, for two logically separate
purposes: to supply the noncollapse needed to select the finite `R / 4`
slice, and to realize the two scalar limit invariants.  The latter continuity
hypothesis does not assert convergence of metrics or an Einstein limit.

The remaining analytic endpoint hypotheses are explicit: global ordinary
quotient evolution transports the finite floor, while global improved
quotient evolution and integrability of the selected-base maximum force its
decay. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily_of_hamilton_improvement
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hImprovedMaximumIntegrable : ∀ t : ℝ, 0 ≤ t →
      GlobalRicciEigenvalueFloor3 (gt t) (1 / 4) →
      IntegrableOn (tracelessPinchingMaximumTrack gt t 0) (Ici 0))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨t0, ht0, hInitFloor, _hPositive, _hQuotient⟩ :=
    exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily
      gt metric parameter hRealize compactControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
  have hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x := by
    intro s hs x
    exact hrho.trans_le
      (hScalarLower (t0 + s) (add_nonneg ht0 hs) x)
  have hForwardFloor : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) (1 / 6) :=
    globalRicciEigenvalueFloor_one_sixth_forward_of_global_one_fourth_initial_floor
      gt hInitFloor hRpos (hQCont t0 ht0) (hQTwo t0 ht0)
        (hQEvol t0 ht0)
  exact
    positiveEinsteinMetric3_of_hamilton_one_sixth_forward_improvement_of_integrableMaximum_of_compact_parameterization
      (gt := gt) (t0 := t0) (c := rho) hrho
      (fun s hs x ↦ hScalarLower (t0 + s) (add_nonneg ht0 hs) x)
      (fun s hs ↦ by
        simpa only [add_assoc] using
          hTQCont (t0 + s) (add_nonneg ht0 hs))
      (fun s hs x ↦ hTQTwo (t0 + s) (add_nonneg ht0 hs) x)
      (fun s hs x ↦ hTQEvol (t0 + s) (add_nonneg ht0 hs) x)
      hForwardFloor (hImprovedMaximumIntegrable t0 ht0 hInitFloor)
      metric (fun s ↦ parameter (t0 + s))
      (fun s _hs ↦ hRealize (t0 + s)) hInvariantContinuous

/-- Compact-parameterization compatibility endpoint with decay supplied by
finite dissipation rather than an integrability hypothesis on the improved
maximum.  The compact family supplies both noncollapse and a convenient
continuous realization of the two limit invariants. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily_of_hamilton_improvement_of_subsequence_decay
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨t0, ht0, hInitFloor, _hPositive, _hQuotient⟩ :=
    exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily
      gt metric parameter hRealize compactControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
  have hForwardScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      rho ≤ (gt (t0 + s)).scalarAt x :=
    fun s hs x ↦ hScalarLower (t0 + s) (add_nonneg ht0 hs) x
  have hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x :=
    fun s hs x ↦ hrho.trans_le (hForwardScalarLower s hs x)
  have hForwardFloor : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) (1 / 6) :=
    globalRicciEigenvalueFloor_one_sixth_forward_of_global_one_fourth_initial_floor
      gt hInitFloor hRpos (hQCont t0 ht0) (hQTwo t0 ht0)
        (hQEvol t0 ht0)
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes
      parameter gt hRealize
  have hTQContForward : ∀ s ∈ Ici (0 : ℝ),
      Continuous ↿(fun tau (x : M) ↦
        (gt ((t0 + s) + tau)).tracelessPinchingAt x 0) := by
    intro s hs
    simpa only [add_assoc] using
      hTQCont (t0 + s) (add_nonneg ht0 hs)
  have hTQTwoForward : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x :=
    fun s hs x ↦ hTQTwo (t0 + s) (add_nonneg ht0 hs) x
  have hTQEvolForward : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + s) x 0
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x) :=
    fun s hs x ↦ hTQEvol (t0 + s) (add_nonneg ht0 hs) x
  have hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) :=
    tracelessPinchingMaximumTrack_tendsto_zero_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_uniformNoncollapse_of_hamilton_forward_improvement
      (gt := gt) (t0 := t0) (A := A) (B := B) (rho := rho)
      hrho hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hNoncollapse hForwardScalarLower
      hTQContForward hTQTwoForward hTQEvolForward hForwardFloor
  exact
    positiveEinsteinMetric3_of_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
      (gt := gt) (t0 := t0) (c := rho) hrho hMaximumZero
      hForwardScalarLower metric (fun s ↦ parameter (t0 + s))
      (fun s _hs ↦ hRealize (t0 + s)) hInvariantContinuous

/-- Finite dissipation and compact reference control produce a positive
Einstein metric from compactness of only the integer-time invariant-pair
range after the internally selected pinched time.

The compact metric family is used here solely to prove noncollapse for the
finite-time concentration argument.  It is not used to realize the limit,
and neither continuity of the invariant pair on that family nor separate
integrability of its maximum is assumed. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hInvariantPairRangeCompact : ∀ t : ℝ, 0 ≤ t → IsCompact
      (Set.range fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t + (i : ℝ))))) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨t0, ht0, hInitFloor, _hPositive, _hQuotient⟩ :=
    exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily
      gt metric parameter hRealize compactControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
  have hForwardScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      rho ≤ (gt (t0 + s)).scalarAt x :=
    fun s hs x ↦ hScalarLower (t0 + s) (add_nonneg ht0 hs) x
  have hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x :=
    fun s hs x ↦ hrho.trans_le (hForwardScalarLower s hs x)
  have hForwardFloor : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) (1 / 6) :=
    globalRicciEigenvalueFloor_one_sixth_forward_of_global_one_fourth_initial_floor
      gt hInitFloor hRpos (hQCont t0 ht0) (hQTwo t0 ht0)
        (hQEvol t0 ht0)
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes
      parameter gt hRealize
  have hTQContForward : ∀ s ∈ Ici (0 : ℝ),
      Continuous ↿(fun tau (x : M) ↦
        (gt ((t0 + s) + tau)).tracelessPinchingAt x 0) := by
    intro s hs
    simpa only [add_assoc] using
      hTQCont (t0 + s) (add_nonneg ht0 hs)
  have hTQTwoForward : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x :=
    fun s hs x ↦ hTQTwo (t0 + s) (add_nonneg ht0 hs) x
  have hTQEvolForward : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + s) x 0
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x) :=
    fun s hs x ↦ hTQEvol (t0 + s) (add_nonneg ht0 hs) x
  have hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) :=
    tracelessPinchingMaximumTrack_tendsto_zero_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_uniformNoncollapse_of_hamilton_forward_improvement
      (gt := gt) (t0 := t0) (A := A) (B := B) (rho := rho)
      hrho hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hNoncollapse hForwardScalarLower
      hTQContForward hTQTwoForward hTQEvolForward hForwardFloor
  exact
    positiveEinsteinMetric3_of_relativePinchingMaximum_tendsto_zero_of_compact_invariantPair_sequence_range
      (gt := gt) (t0 := t0) (c := rho) hrho hMaximumZero
      hForwardScalarLower (hInvariantPairRangeCompact t0 ht0)

/-- Tensor-level compact reference control suffices for the same end-to-end
positive-Einstein conclusion.  The distance comparison needed by the
finite-slice concentration theorem is constructed from pointwise quadratic-
form domination, rather than retained as an input. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hImprovedMaximumIntegrable : ∀ t : ℝ, 0 ≤ t →
      GlobalRicciEigenvalueFloor3 (gt t) (1 / 4) →
      IntegrableOn (tracelessPinchingMaximumTrack gt t 0) (Ici 0))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨distanceControl⟩ := compactControl.exists_distanceFamilyData
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily_of_hamilton_improvement
      gt metric parameter hRealize distanceControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
      hQCont hQTwo hQEvol hTQCont hTQTwo hTQEvol
      hImprovedMaximumIntegrable hInvariantContinuous

/-- Tensor-reference compatibility wrapper for the finite-dissipation
subsequence-decay endpoint.  Pointwise tensor domination constructs the
distance-family control used by the distance-reference theorem. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_subsequence_decay
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨distanceControl⟩ := compactControl.exists_distanceFamilyData
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily_of_hamilton_improvement_of_subsequence_decay
      gt metric parameter hRealize distanceControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
      hQCont hQTwo hQEvol hTQCont hTQTwo hTQEvol
      hInvariantContinuous

/-- Tensor-level compact reference control is also sufficient for the
range-only endpoint.  Its sole role is noncollapse at the finite-slice step;
the Einstein limit is realized from the compact integer-time invariant-pair
range itself. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hInvariantPairRangeCompact : ∀ t : ℝ, 0 ≤ t → IsCompact
      (Set.range fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t + (i : ℝ))))) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨distanceControl⟩ := compactControl.exists_distanceFamilyData
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
      gt metric parameter hRealize distanceControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
      hQCont hQTwo hQEvol hTQCont hTQTwo hTQEvol
      hInvariantPairRangeCompact

/-- The strongest tensor-reference/range-only normalized-flow endpoint
constructs a unit-constant-sectional-curvature metric before any sphere
recognition theorem is invoked. -/
theorem exists_unitConstantCurvature_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hInvariantPairRangeCompact : ∀ t : ℝ, 0 ≤ t → IsCompact
      (Set.range fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t + (i : ℝ))))) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
      gt metric parameter hRealize compactControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
      hQCont hQTwo hQEvol hTQCont hTQTwo hTQEvol
      hInvariantPairRangeCompact

/-- End-to-end sphere conclusion for the strongest normalized-flow consumer.

The final boundary remains explicit: `UnitConstantCurvatureSphereRecognition3`
is exactly the space-form recognition theorem that turns the constructed
unit-curvature metric into the statement-layer homeomorphism with `S³`.
No diffeomorphism claim is made because the repository recognition interface
returns a homeomorphism, which is the payload used by `PoincareConjecture`. -/
theorem sphereConclusion_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x)
    (hQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).pinchingQuotientAt x))
    (hQTwo : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t + s)).pinchingQuotientAt y) x)
    (hQEvol : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
        gt (t + s) x
          ((gt (t + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hTQCont : ∀ t : ℝ, 0 ≤ t →
      Continuous ↿(fun s (x : M) ↦
        (gt (t + s)).tracelessPinchingAt x 0))
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hTQEvol : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt t x 0 ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hInvariantPairRangeCompact : ∀ t : ℝ, 0 ≤ t → IsCompact
      (Set.range fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t + (i : ℝ)))))
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
      gt metric parameter hRealize compactControl hrho hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hScalarLower
      hQCont hQTwo hQEvol hTQCont hTQTwo hTQEvol
      hInvariantPairRangeCompact

end Poincare
