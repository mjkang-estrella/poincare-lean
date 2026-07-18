import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.MetricFlowJointPinchingEvolution

/-!
# Joint-continuity criteria for the normalized-flow invariant pair

The compact pinching-limit endpoint only asks for continuity, in a compact
metric parameter, of the spatial scalar minimum and relative-pinching
maximum.  This file reduces that finite-dimensional premise to concrete joint
continuity on the product of the parameter space and the compact manifold.

The proof is the parametric extreme-value theorem: `IsCompact.continuous_sInf`
and `IsCompact.continuous_sSup` make the infimum and supremum over a fixed
compact spatial fiber continuous in the parameter.
-/

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {M : Type u} {K : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [TopologicalSpace K]

/-- Global joint `C³` metric-entry regularity of an actual real-time metric
flow proves joint continuity of both curvature quantities used by the
compact-family criterion.

This is the strongest currently proof-bearing derivation in the repository.
Its parameter is real time; it does not by itself extend these quantities to
an arbitrary compact parameter space `K`. -/
theorem continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    Continuous ↿(fun t (x : M) ↦ (gt t).scalarAt x) ∧
      Continuous ↿(fun t (x : M) ↦
        (gt t).tracelessRicciNormSqAt x) := by
  constructor
  · rw [continuous_iff_continuousAt]
    rintro ⟨t, x⟩
    exact
      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
        (hJoint t x)
  · rw [continuous_iff_continuousAt]
    rintro ⟨t, x⟩
    have hRic :=
      continuousAt_ricciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
        (hJoint t x)
    have hScalar :=
      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
        (hJoint t x)
    simpa [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt] using
      hRic.sub ((hScalar.pow 2).div_const 3)

/-- Joint continuity of scalar curvature over `K × M` makes its spatial
minimum continuous in the compact-family parameter. -/
theorem continuous_scalarMinimumAt_comp_of_joint_scalarAt
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hScalar : Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x)) :
    Continuous (fun k ↦ scalarMinimumAt (metric k)) := by
  simpa only [scalarMinimumAt, Set.image_univ] using
    (isCompact_univ : IsCompact (Set.univ : Set M)).continuous_sInf hScalar

/-- Joint continuity of squared traceless Ricci over `K × M` makes its
absolute spatial maximum continuous in the compact-family parameter. -/
theorem continuous_tracelessRicciMaximumAt_comp_of_joint_tracelessRicciNormSqAt
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    Continuous (fun k ↦ tracelessRicciMaximumAt (metric k)) := by
  simpa only [tracelessRicciMaximumAt, Set.image_univ] using
    (isCompact_univ : IsCompact (Set.univ : Set M)).continuous_sSup hTraceless

/-- Joint scalar and squared-traceless-Ricci continuity implies continuity
of the denominator-free invariant pair used by the absolute-energy compact
limit endpoint. -/
theorem continuous_closedMetricScalarMinimumTracelessRicciMaximumPair_comp_of_joint
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hScalar : Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x))
    (hTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    Continuous (fun k ↦
      closedMetricScalarMinimumTracelessRicciMaximumPair (metric k)) := by
  exact
    (continuous_scalarMinimumAt_comp_of_joint_scalarAt metric hScalar).prodMk
      (continuous_tracelessRicciMaximumAt_comp_of_joint_tracelessRicciNormSqAt
        metric hTraceless)

/-- Joint continuity of exponent-zero improved pinching over `K × M`
makes its spatial maximum continuous in the compact-family parameter. -/
theorem continuous_tracelessPinchingMaximumAt_zero_comp_of_joint
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hPinching : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0)) :
    Continuous (fun k ↦ tracelessPinchingMaximumAt (metric k) 0) := by
  simpa only [tracelessPinchingMaximumAt, Set.image_univ] using
    (isCompact_univ : IsCompact (Set.univ : Set M)).continuous_sSup hPinching

/-- Concrete joint scalar/pinching continuity implies continuity of exactly
the invariant pair consumed by the sampled compact limit. -/
theorem continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_joint
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hScalar : Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x))
    (hPinching : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0)) :
    Continuous (fun k ↦
      closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)) := by
  exact
    (continuous_scalarMinimumAt_comp_of_joint_scalarAt metric hScalar).prodMk
      (continuous_tracelessPinchingMaximumAt_zero_comp_of_joint
        metric hPinching)

/-- Joint continuity of scalar curvature and squared traceless Ricci gives
joint continuity of exponent-zero pinching wherever scalar curvature is
positive. -/
theorem continuous_joint_tracelessPinchingAt_zero_of_joint_scalarAt_of_joint_tracelessRicciNormSqAt_of_pos
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hScalar : Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x))
    (hTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x))
    (hScalarPos : ∀ k : K, ∀ x : M, 0 < (metric k).scalarAt x) :
    Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0) := by
  have hQuotient : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x /
        ((metric k).scalarAt x) ^ 2) :=
    hTraceless.div (hScalar.pow 2) fun p ↦
      pow_ne_zero 2 (hScalarPos p.1 p.2).ne'
  simpa only [ClosedSmoothRiemannianMetric.tracelessPinchingAt,
    sub_zero, Real.rpow_two] using hQuotient

/-- Joint scalar and traceless-Ricci continuity, together with positivity of
scalar curvature throughout the compact family, discharge the invariant-pair
continuity hypothesis used by the sampled Einstein endpoint. -/
theorem continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_joint_scalarAt_of_joint_tracelessRicciNormSqAt_of_pos
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hScalar : Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x))
    (hTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x))
    (hScalarPos : ∀ k : K, ∀ x : M, 0 < (metric k).scalarAt x) :
    Continuous (fun k ↦
      closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)) := by
  apply
    continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_joint
      metric hScalar
  exact
    continuous_joint_tracelessPinchingAt_zero_of_joint_scalarAt_of_joint_tracelessRicciNormSqAt_of_pos
      metric hScalar hTraceless hScalarPos

/-- Global joint `C³` metric-entry regularity and positive scalar curvature
make the scalar-minimum / relative-pinching-maximum pair of an actual
real-time metric flow continuous in time.

This is a time-track statement.  Unlike an ambient compact-family hypothesis,
it gives no compactness for an unbounded forward tail. -/
theorem continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_global_metricEntriesJointContDiffAt_three_of_scalarPos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hScalarPos : ∀ t : ℝ, ∀ x : M, 0 < (gt t).scalarAt x) :
    Continuous (fun t ↦
      closedMetricScalarMinimumRelativePinchingMaximumPair (gt t)) := by
  obtain ⟨hScalar, hTraceless⟩ :=
    continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
      gt hJoint
  exact
    continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_joint_scalarAt_of_joint_tracelessRicciNormSqAt_of_pos
      gt hScalar hTraceless hScalarPos

/-- The invariant-pair image of every compact real-time window is compact
under global joint `C³` metric-entry regularity and positive scalar curvature.

The interval is bounded: this result is genuine finite-window compactness and
does not establish precompactness of the forward tail `Ici a`. -/
theorem isCompact_closedMetricScalarMinimumRelativePinchingMaximumPair_image_Icc_of_global_metricEntriesJointContDiffAt_three_of_scalarPos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hScalarPos : ∀ t : ℝ, ∀ x : M, 0 < (gt t).scalarAt x)
    (a b : ℝ) :
    IsCompact
      ((fun t ↦
          closedMetricScalarMinimumRelativePinchingMaximumPair (gt t)) ''
        Icc a b) := by
  exact
    isCompact_Icc.image_of_continuousOn
      (continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_global_metricEntriesJointContDiffAt_three_of_scalarPos
        gt hJoint hScalarPos).continuousOn

/-- Global joint `C³` metric-entry regularity and scalar positivity only on
forward time make the invariant-pair track continuous on `Ici 0`.

Passing to the subtype `Ici 0` is essential here: forward positivity cannot
justify continuity of the pinching quotient at negative times. -/
theorem continuousOn_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_global_metricEntriesJointContDiffAt_three_of_forwardScalarPos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x) :
    ContinuousOn
      (fun t ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (gt t))
      (Ici 0) := by
  obtain ⟨hScalar, hTraceless⟩ :=
    continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
      gt hJoint
  have hInclusion : Continuous (fun p : Ici (0 : ℝ) × M ↦
      ((p.1.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hScalarForward : Continuous ↿(fun (t : Ici (0 : ℝ)) (x : M) ↦
      (gt t.1).scalarAt x) :=
    by simpa only [Function.comp_apply] using hScalar.comp hInclusion
  have hTracelessForward : Continuous ↿(fun (t : Ici (0 : ℝ)) (x : M) ↦
      (gt t.1).tracelessRicciNormSqAt x) :=
    by simpa only [Function.comp_apply] using hTraceless.comp hInclusion
  have hScalarPosForward : ∀ t : Ici (0 : ℝ), ∀ x : M,
      0 < (gt t.1).scalarAt x := fun t x ↦
    hForwardScalarPos t.1 t.2 x
  rw [continuousOn_iff_continuous_restrict]
  exact
    continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_joint_scalarAt_of_joint_tracelessRicciNormSqAt_of_pos
      (fun t : Ici (0 : ℝ) ↦ gt t.1)
      hScalarForward hTracelessForward hScalarPosForward

/-- Every nonnegative compact time window has compact invariant-pair image
under global joint `C³` metric-entry regularity and forward scalar positivity.

No uniformity as the right endpoint tends to infinity is claimed, so this is
not precompactness of the forward tail. -/
theorem isCompact_closedMetricScalarMinimumRelativePinchingMaximumPair_image_Icc_of_global_metricEntriesJointContDiffAt_three_of_forwardScalarPos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    {a b : ℝ} (ha : 0 ≤ a) :
    IsCompact
      ((fun t ↦
          closedMetricScalarMinimumRelativePinchingMaximumPair (gt t)) ''
        Icc a b) := by
  apply isCompact_Icc.image_of_continuousOn
  exact
    (continuousOn_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_global_metricEntriesJointContDiffAt_three_of_forwardScalarPos
      gt hJoint hForwardScalarPos).mono fun t ht ↦ ha.trans ht.1

end Poincare
