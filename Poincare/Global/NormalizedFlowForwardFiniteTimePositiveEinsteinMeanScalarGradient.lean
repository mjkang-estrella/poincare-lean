import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalar
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient
import Poincare.Global.NormalizedFlowDissipationDifferentialDecay
import Poincare.Global.EinsteinNormalization

/-!
# Forward mean-scalar Einstein endpoint from geometric derivative control

This module derives both concentration Lipschitz bounds and noncollapse on the
forward ray.  Every time-indexed geometric hypothesis is carried by the
subtype `Ici 0`: no regularity instance, flow equation, compact realization,
derivative identity, curvature bound, or scalar floor is assumed at negative
time.

Joint scalar and squared-traceless-Ricci continuity on the compact reference
family give the required uniform zeroth-order bounds.  Joint `C³` metric
entries and the normalized-flow equation give spatial `C¹` regularity on each
forward slice.  A subtype-indexed full covariant-Ricci derivative bound then
supplies the scalar and traceless-Ricci Lipschitz estimates.  Compact tensor
control supplies forward noncollapse, after which the denominator-free raw
forward endpoint applies.
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

omit [SecondCountableTopology M] in
/-- At one proof-carrying forward time, joint `C³` metric entries and the
normalized-flow equation give spatial `C²` regularity of squared traceless
Ricci.  Only the Levi-Civita regularity instance for that forward slice is
used. -/
theorem contMDiffAt_two_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three_Ici
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (t : Ici (0 : ℝ)) (x : M)
    [∀ s : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt s.1).leviCivita 1]
    (hFlow : ∀ y : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t.1 y 3) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t.1).tracelessRicciNormSqAt y) x := by
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      (gt t.1).leviCivita 1 :=
    (inferInstance : ∀ s : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt s.1).leviCivita 1) t
  let g : ClosedSmoothRiemannianMetric 3 M := gt t.1
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t.1 y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
      hFlow hEntries y
  have hNorm2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x :=
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g x (hRicC2 x)
  have hScalar2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x :=
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries x
  exact contMDiffAt_two_tracelessRicciNormSqAt g x hNorm2 hScalar2

omit [SecondCountableTopology M] in
/-- Forward normalized flow plus joint `C³` metric entries supplies spatial
`C¹` scalar curvature on the subtype-indexed metric family. -/
theorem uniformScalarCurvatureCOne_of_normalizedRicciFlow_joint_metric_entries_three_Ici
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hJoint : ∀ t : Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t.1 x 3) :
    UniformScalarCurvatureCOne
      (fun t : Ici (0 : ℝ) ↦ gt t.1) := by
  intro t x
  exact
    (scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      (hFlow t)
      (fun y ↦
        timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
          (hJoint t y)) x).of_le (by norm_num)

omit [SecondCountableTopology M] in
/-- Forward normalized flow plus joint `C³` metric entries supplies spatial
`C¹` squared traceless-Ricci norm on the subtype-indexed metric family. -/
theorem uniformTracelessRicciEnergyCOne_of_normalizedRicciFlow_joint_metric_entries_three_Ici
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt t.1).leviCivita 1]
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hJoint : ∀ t : Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t.1 x 3) :
    UniformTracelessRicciEnergyCOne
      (fun t : Ici (0 : ℝ) ↦ gt t.1) := by
  intro t x
  exact
    (contMDiffAt_two_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three_Ici
      t x (hFlow t) (hJoint t)).of_le (by norm_num)

/-- Strongest geometric forward-ray mean-scalar endpoint.

The compact family automatically bounds centered scalar and squared
traceless Ricci.  Forward joint `C³` entries automatically provide the two
spatial `C¹` fields.  The only derivative-size input is full covariant-Ricci
control on the proof-carrying forward subtype; it generates both required
Lipschitz bounds. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ),
      metric (parameter t) = gt t.1)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {D c : ℝ}
    [∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt t.1).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hJointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t.1 x 3)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hFullCovariantRicci :
      UniformCovariantRicciDerivativeNormBound
        (fun t : Ici (0 : ℝ) ↦ gt t.1) D)
    (hMeanLower : ∀ t : Ici (0 : ℝ),
      c ≤ meanScalar (gt t.1))
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨A, hA, hTracelessMetric⟩ :=
    exists_pos_uniform_tracelessRicciNormSqAt_bound_of_compact_joint
      metric hJointTraceless
  have hTracelessRicci : UniformTracelessRicciNormBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1) A := by
    refine ⟨hA, ?_⟩
    intro t x
    simpa only [hRealize t] using hTracelessMetric (parameter t) x
  obtain ⟨C, hC, hCenteredMetric⟩ :=
    exists_pos_uniform_centeredScalar_bound_of_compact_joint_scalar
      metric hJointScalar
  have hCenteredFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      |(gt t.1).scalarAt x - meanScalar (gt t.1)| ≤ C := by
    intro t x
    simpa only [hRealize t] using hCenteredMetric (parameter t) x
  have hScalarCOne : UniformScalarCurvatureCOne
      (fun t : Ici (0 : ℝ) ↦ gt t.1) :=
    uniformScalarCurvatureCOne_of_normalizedRicciFlow_joint_metric_entries_three_Ici
      hFlow hJointMetricEntries
  have hTracelessCOne : UniformTracelessRicciEnergyCOne
      (fun t : Ici (0 : ℝ) ↦ gt t.1) :=
    uniformTracelessRicciEnergyCOne_of_normalizedRicciFlow_joint_metric_entries_three_Ici
      hFlow hJointMetricEntries
  have hScalarGradient : UniformClosedRiemannianMFDerivBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1)
      (fun t x ↦ (gt t.1).scalarAt x) (3 * D) :=
    uniformClosedRiemannianMFDerivBound_scalarAt_of_covariantRicciDerivativeNormBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1) hScalarCOne
        hFullCovariantRicci
  have hScalarVarianceLipschitz :
      ForwardUniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2)
        (2 * C * (3 * D)) :=
    uniformClosedRiemannianLipschitzBound_centeredScalarSq_of_centeredBound_of_scalarMFDerivBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1) hC hCenteredFlow hScalarGradient
  have hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1) A D :=
    uniformTracelessRicciAndCovariantDerivativeNormBound_of_tracelessRicci_of_covariantRicciDerivative
      (fun t : Ici (0 : ℝ) ↦ gt t.1) hTracelessRicci
        hFullCovariantRicci
  have hTracelessLipschitz :
      ForwardUniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * D) :=
    uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1) hTracelessCOne hBounds
  have hNoncollapse : ForwardUniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes parameter
      (fun t : Ici (0 : ℝ) ↦ gt t.1) hRealize
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization
      gt metric parameter hRealize hc
      (fun t ht ↦ hFlow ⟨t, ht⟩)
      (fun t ht ↦ hDifferentiateMovingTotalScalar ⟨t, ht⟩)
      (fun t ht ↦ hDifferentiateMovingVolume ⟨t, ht⟩)
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hNoncollapse (fun t ht ↦ hMeanLower ⟨t, ht⟩)
      hJointScalar hJointTraceless

/-- A coercive differential inequality for the absolute dissipation removes
the remaining abstract finite-dissipation premise from the strongest
geometric forward endpoint.  Both quantitative hypotheses are indexed by the
proof-carrying forward subtype. -/
theorem positiveEinsteinMetric3_of_differentialAbsoluteDissipationDecay_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ),
      metric (parameter t) = gt t.1)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {D c : ℝ}
    [∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt t.1).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hJointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t.1 x 3)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (dissipationDerivative : ℝ → ℝ)
    {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDerivative : ∀ t : Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (dissipationDerivative t.1) t.1)
    (hDifferentialInequality : ∀ t : Ici (0 : ℝ),
      dissipationDerivative t.1 ≤
        -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t.1)
    (hFullCovariantRicci :
      UniformCovariantRicciDerivativeNormBound
        (fun t : Ici (0 : ℝ) ↦ gt t.1) D)
    (hMeanLower : ∀ t : Ici (0 : ℝ),
      c ≤ meanScalar (gt t.1))
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    PositiveEinsteinMetric3 M := by
  have hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0) :=
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
      gt dissipationDerivative hrate
      (fun t ht ↦ hDissipationDerivative ⟨t, ht⟩)
      (fun t ht ↦ hDifferentialInequality ⟨t, ht⟩)
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation hFullCovariantRicci
      hMeanLower hJointScalar hJointTraceless

section Consequences

variable [Nonempty M] [SimplyConnectedSpace M]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
variable (metric : K → ClosedSmoothRiemannianMetric 3 M)
variable (parameter : Ici (0 : ℝ) → K)
variable (hRealize : ∀ t : Ici (0 : ℝ),
  metric (parameter t) = gt t.1)
variable (compactControl : CompactReferenceMetricTensorFamilyData K metric)
variable {D c : ℝ}
variable [∀ t : Ici (0 : ℝ),
  CovariantDerivative.ContMDiffCovariantDerivative
    (gt t.1).leviCivita 1]
variable (hc : 0 < c)
variable (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
variable (hJointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
  MetricEntriesJointContDiffAt gt t.1 x 3)
variable (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
  HasDerivAt (fun s ↦ totalScalar (gt s))
    (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
variable (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
  HasDerivAt (fun s ↦ totalVolume (gt s))
    (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
variable (hFiniteDissipation :
  IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
variable (hFullCovariantRicci :
  UniformCovariantRicciDerivativeNormBound
    (fun t : Ici (0 : ℝ) ↦ gt t.1) D)
variable (hMeanLower : ∀ t : Ici (0 : ℝ),
  c ≤ meanScalar (gt t.1))
variable (hJointScalar : Continuous ↿(fun k (x : M) ↦
  (metric k).scalarAt x))
variable (hJointTraceless : Continuous ↿(fun k (x : M) ↦
  (metric k).tracelessRicciNormSqAt x))

include gt metric parameter hRealize compactControl hc hFlow
  hJointMetricEntries hDifferentiateMovingTotalScalar
  hDifferentiateMovingVolume hFiniteDissipation hFullCovariantRicci
  hMeanLower hJointScalar hJointTraceless

/-- The geometric forward endpoint normalizes its positive Einstein metric
to sectional curvature exactly `1`. -/
theorem exists_unitConstantCurvature_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation hFullCovariantRicci
      hMeanLower hJointScalar hJointTraceless

/-- With the explicit unit-curvature recognition boundary, the same
forward-only route yields a homeomorphism to the unit `3`-sphere. -/
theorem sphereConclusion_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation hFullCovariantRicci
      hMeanLower hJointScalar hJointTraceless

end Consequences

section DifferentialDecayConsequences

variable [Nonempty M] [SimplyConnectedSpace M]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
variable (metric : K → ClosedSmoothRiemannianMetric 3 M)
variable (parameter : Ici (0 : ℝ) → K)
variable (hRealize : ∀ t : Ici (0 : ℝ),
  metric (parameter t) = gt t.1)
variable (compactControl : CompactReferenceMetricTensorFamilyData K metric)
variable {D c : ℝ}
variable [∀ t : Ici (0 : ℝ),
  CovariantDerivative.ContMDiffCovariantDerivative
    (gt t.1).leviCivita 1]
variable (hc : 0 < c)
variable (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
variable (hJointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
  MetricEntriesJointContDiffAt gt t.1 x 3)
variable (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
  HasDerivAt (fun s ↦ totalScalar (gt s))
    (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
variable (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
  HasDerivAt (fun s ↦ totalVolume (gt s))
    (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
variable (dissipationDerivative : ℝ → ℝ)
variable {rate : ℝ} (hrate : 0 < rate)
variable (hDissipationDerivative : ∀ t : Ici (0 : ℝ),
  HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt)
    (dissipationDerivative t.1) t.1)
variable (hDifferentialInequality : ∀ t : Ici (0 : ℝ),
  dissipationDerivative t.1 ≤
    -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t.1)
variable (hFullCovariantRicci :
  UniformCovariantRicciDerivativeNormBound
    (fun t : Ici (0 : ℝ) ↦ gt t.1) D)
variable (hMeanLower : ∀ t : Ici (0 : ℝ),
  c ≤ meanScalar (gt t.1))
variable (hJointScalar : Continuous ↿(fun k (x : M) ↦
  (metric k).scalarAt x))
variable (hJointTraceless : Continuous ↿(fun k (x : M) ↦
  (metric k).tracelessRicciNormSqAt x))

include gt metric parameter hRealize compactControl hc hFlow
  hJointMetricEntries hDifferentiateMovingTotalScalar
  hDifferentiateMovingVolume dissipationDerivative hrate
  hDissipationDerivative hDifferentialInequality hFullCovariantRicci
  hMeanLower hJointScalar hJointTraceless

/-- Differential absolute-dissipation decay and the geometric forward data
produce a unit-sectional-curvature metric. -/
theorem exists_unitConstantCurvature_of_differentialAbsoluteDissipationDecay_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_differentialAbsoluteDissipationDecay_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume dissipationDerivative hrate
      hDissipationDerivative hDifferentialInequality hFullCovariantRicci
      hMeanLower hJointScalar hJointTraceless

/-- Adding only the explicit unit-curvature recognition boundary to the
differential-decay route yields the unit `3`-sphere conclusion. -/
theorem sphereConclusion_of_differentialAbsoluteDissipationDecay_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_differentialAbsoluteDissipationDecay_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume dissipationDerivative hrate
      hDissipationDerivative hDifferentialInequality hFullCovariantRicci
      hMeanLower hJointScalar hJointTraceless

end DifferentialDecayConsequences

end Poincare
