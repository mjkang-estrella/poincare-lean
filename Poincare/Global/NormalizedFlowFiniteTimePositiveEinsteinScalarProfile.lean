import Poincare.Global.NormalizedFlowFiniteTimePositiveEinstein
import Poincare.Global.NormalizedFlowScalarLowerProfile

/-!
# Positive-Einstein endpoint from an initial positive scalar profile

This file removes the explicit uniform scalar lower bound from the strongest
normalized-flow consumer.  Initial pointwise scalar positivity, the assembled
normalized scalar evolution, and an upper bound for the normalization
primitive produce the required positive constant floor.  The existing
compact integer-time invariant-pair range and sphere-recognition boundaries
are then reused unchanged.
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

/-- The strongest tensor-reference/range-only positive-Einstein endpoint with
the uniform scalar floor derived from initial positivity and a bounded-above
normalization primitive.

The compact invariant-pair range remains an explicit realization boundary;
this theorem changes only the provenance of the positive scalar floor. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B C : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt tau).scalarAt x))
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt tau)) tau)
    (hPrimitiveUpper : ∀ tau ∈ Ici (0 : ℝ),
      normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
    (hInitialPos : ∀ x : M, 0 < (gt 0).scalarAt x)
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
  obtain ⟨rhoFloor, hrhoFloor, hScalarLower⟩ :=
    exists_uniform_normalizedFlow_scalar_lower_of_normalizedFlow_of_globalLichnerowicz_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
      (gt := gt) (t0 := 0) (C := C) hFlow hLichnerowicz
      (by simpa only [zero_add] using hScalarContinuous)
      normalizationPrimitive hPrimitiveContinuous
      (by simpa only [zero_add] using hPrimitiveDerivative)
      hPrimitiveUpper hInitialPos
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range
      gt metric parameter hRealize compactControl hrhoFloor hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds
      (fun t ht x ↦ by
        simpa only [zero_add] using hScalarLower t ht x)
      hQCont hQTwo hQEvol hTQCont hTQTwo hTQEvol
      hInvariantPairRangeCompact

/-- The scalar-profile endpoint constructs a unit-sectional-curvature metric
without changing the geometric recognition boundary. -/
theorem exists_unitConstantCurvature_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B C : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt tau).scalarAt x))
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt tau)) tau)
    (hPrimitiveUpper : ∀ tau ∈ Ici (0 : ℝ),
      normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
    (hInitialPos : ∀ x : M, 0 < (gt 0).scalarAt x)
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
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
      gt metric parameter hRealize compactControl hFlow hLichnerowicz
      hScalarContinuous normalizationPrimitive hPrimitiveContinuous
      hPrimitiveDerivative hPrimitiveUpper hInitialPos
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hQCont hQTwo hQEvol
      hTQCont hTQTwo hTQEvol hInvariantPairRangeCompact

/-- End-to-end sphere conclusion with the scalar floor derived from initial
positivity and the bounded normalization primitive.

`UnitConstantCurvatureSphereRecognition3` remains the final explicit
space-form recognition premise, and the conclusion remains the statement-layer
homeomorphism to the unit `3`-sphere. -/
theorem sphereConclusion_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B C : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hScalarContinuous :
      Continuous ↿(fun tau (x : M) ↦ (gt tau).scalarAt x))
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ tau ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt tau)) tau)
    (hPrimitiveUpper : ∀ tau ∈ Ici (0 : ℝ),
      normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
    (hInitialPos : ∀ x : M, 0 < (gt 0).scalarAt x)
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
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_hamilton_improvement_of_compact_integer_invariant_pair_range_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
      gt metric parameter hRealize compactControl hFlow hLichnerowicz
      hScalarContinuous normalizationPrimitive hPrimitiveContinuous
      hPrimitiveDerivative hPrimitiveUpper hInitialPos
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hCOne hBounds hQCont hQTwo hQEvol
      hTQCont hTQTwo hTQEvol hInvariantPairRangeCompact

end Poincare
