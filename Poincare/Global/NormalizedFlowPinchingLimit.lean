import Poincare.Global.NormalizedFlowImprovedPinchingDecay
import Poincare.Global.PinchedLimitPositiveEinstein

/-!
# Realizing quantitative Hamilton pinching as a positive Einstein limit

The improved maximum principle and its decay consumers produce a scalar
statement about the evolving metrics.  This file gives that statement an
honest compactness endpoint.

The core compactness hypothesis transports only two existing scalar
invariants:

* the spatial scalar-curvature minimum;
* the spatial maximum of `|Ric°|² / R²`, i.e. improved pinching at
  exponent zero.

If the first stays uniformly positive and the second tends to zero, a compact
realized range for their integer-time pair sequence supplies a smooth
positive-scalar metric with vanishing traceless Ricci tensor.  This is exactly
the reduced Hamilton limit payload, hence a positive Einstein metric.  No
convergence of the full metric orbit and no Einstein conclusion is included in
the compactness premise.  A compact metric parameterization remains available
below as a convenient sufficient-condition wrapper.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [CompactSpace M] [ConnectedSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The two scalar invariants consumed by the pinching-limit realization. -/
noncomputable def closedMetricScalarMinimumRelativePinchingMaximumPair
    (g : ClosedSmoothRiemannianMetric 3 M) : ℝ × ℝ :=
  (scalarMinimumAt g, tracelessPinchingMaximumAt g 0)

/-- The spatial supremum of the squared traceless-Ricci norm. -/
noncomputable def tracelessRicciMaximumAt
    (g : ClosedSmoothRiemannianMetric 3 M) : ℝ :=
  sSup (Set.range fun x : M ↦ g.tracelessRicciNormSqAt x)

/-- The scalar minimum and absolute squared-traceless-Ricci maximum.  This
pair avoids every scalar-curvature denominator in the compact limit step. -/
noncomputable def closedMetricScalarMinimumTracelessRicciMaximumPair
    (g : ClosedSmoothRiemannianMetric 3 M) : ℝ × ℝ :=
  (scalarMinimumAt g, tracelessRicciMaximumAt g)

/-- A pointwise scalar lower bound is inherited by the infimum definition of
the closed scalar minimum.  No maximum-principle regularity is needed. -/
theorem le_scalarMinimumAt_of_forall_le_scalarAt
    [Nonempty M]
    (g : ClosedSmoothRiemannianMetric 3 M) {c : ℝ}
    (h : ∀ x : M, c ≤ g.scalarAt x) :
    c ≤ scalarMinimumAt g := by
  obtain ⟨x0⟩ : Nonempty M := inferInstance
  rw [scalarMinimumAt]
  refine le_csInf
    (s := Set.range fun x : M ↦ g.scalarAt x)
    ⟨g.scalarAt x0, ⟨x0, rfl⟩⟩ ?_
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact h x

/-- The scalar infimum lies below every point value using only the existing
continuity of scalar curvature on a compact manifold. -/
theorem scalarMinimumAt_le_scalarAt_of_continuous
    [Nonempty M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    scalarMinimumAt g ≤ g.scalarAt x := by
  obtain ⟨xmin, _hxmin, hmin⟩ :=
    isCompact_univ.exists_isMinOn
      (Set.univ_nonempty)
      (fun y _ ↦ (scalarAt_continuous g).continuousAt.continuousWithinAt)
  rw [scalarMinimumAt_eq_of_isMinOn (g := g) hmin]
  exact hmin trivial

/-- If squared traceless Ricci attains its maximum at `x`, its supremum
definition equals that point value. -/
theorem tracelessRicciMaximumAt_eq_of_isMaxOn
    (g : ClosedSmoothRiemannianMetric 3 M) {x : M}
    (hmax : IsMaxOn (fun y : M ↦ g.tracelessRicciNormSqAt y) Set.univ x) :
    tracelessRicciMaximumAt g = g.tracelessRicciNormSqAt x := by
  let S : Set ℝ := Set.range fun y : M ↦ g.tracelessRicciNormSqAt y
  have hne : S.Nonempty := ⟨g.tracelessRicciNormSqAt x, ⟨x, rfl⟩⟩
  have hupper : ∀ y ∈ S, y ≤ g.tracelessRicciNormSqAt x := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact hmax trivial
  have hbdd : BddAbove S := ⟨g.tracelessRicciNormSqAt x, hupper⟩
  apply le_antisymm
  · exact csSup_le hne hupper
  · exact le_csSup hbdd ⟨x, rfl⟩

/-- Every pointwise squared traceless-Ricci value lies below its compact
spatial maximum. -/
theorem tracelessRicciNormSqAt_le_tracelessRicciMaximumAt
    [Nonempty M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    g.tracelessRicciNormSqAt x ≤ tracelessRicciMaximumAt g := by
  obtain ⟨xmax, _hxmax, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (fun y _ ↦
        (tracelessRicciNormSqAt_continuous g).continuousAt.continuousWithinAt)
  rw [tracelessRicciMaximumAt_eq_of_isMaxOn g hmax]
  exact hmax trivial

/-- The maximum of squared traceless Ricci is nonnegative. -/
theorem tracelessRicciMaximumAt_nonneg
    [Nonempty M]
    (g : ClosedSmoothRiemannianMetric 3 M) :
    0 ≤ tracelessRicciMaximumAt g := by
  obtain ⟨x⟩ : Nonempty M := inferInstance
  exact (g.tracelessRicciNormSqAt_nonneg x (by norm_num)).trans
    (tracelessRicciNormSqAt_le_tracelessRicciMaximumAt g x)

/-- Uniform convergence of squared traceless Ricci to zero makes its spatial
maximum converge to zero. -/
theorem tendsto_tracelessRicciMaximumAt_zero_of_eventually_uniformly_small
    [Nonempty M]
    (g : ℕ → ClosedSmoothRiemannianMetric 3 M)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (g i).tracelessRicciNormSqAt x < epsilon) :
    Tendsto (fun i ↦ tracelessRicciMaximumAt (g i)) atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun i ↦
      ha.trans_le (tracelessRicciMaximumAt_nonneg (g i))
  · intro b hb
    filter_upwards [hUniformSmall b hb] with i hi
    obtain ⟨xmax, _hxmax, hmax⟩ :=
      isCompact_univ.exists_isMaxOn Set.univ_nonempty
        (fun y _ ↦
          (tracelessRicciNormSqAt_continuous (g i)).continuousAt.continuousWithinAt)
    rw [tracelessRicciMaximumAt_eq_of_isMaxOn (g i) hmax]
    exact hi xmax

/-- Improved traceless pinching at exponent zero is exactly the relative
traceless-Ricci anisotropy. -/
theorem ClosedSmoothRiemannianMetric.relativeTracelessRicciAt_eq_tracelessPinchingAt_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    g.relativeTracelessRicciAt x = g.tracelessPinchingAt x 0 := by
  rw [g.relativeTracelessRicciAt_eq, g.tracelessPinchingAt_eq]
  simp only [sub_zero, Real.rpow_two]

/-- Positive scalar curvature makes the exponent-zero improved pinching
quantity continuous without an extra `C²` maximum-principle hypothesis. -/
theorem continuous_tracelessPinchingAt_zero_of_scalarAt_pos
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hRpos : ∀ x : M, 0 < g.scalarAt x) :
    Continuous (fun x : M ↦ g.tracelessPinchingAt x 0) := by
  have hrelative :
      Continuous (fun x : M ↦ g.relativeTracelessRicciAt x) := by
    simpa [ClosedSmoothRiemannianMetric.relativeTracelessRicciAt] using
      (tracelessRicciNormSqAt_continuous g).div
        ((scalarAt_continuous g).pow 2)
        (fun x ↦ pow_ne_zero 2 (hRpos x).ne')
  have hfun :
      (fun x : M ↦ g.tracelessPinchingAt x 0) =
        fun x : M ↦ g.relativeTracelessRicciAt x := by
    funext x
    exact (g.relativeTracelessRicciAt_eq_tracelessPinchingAt_zero x).symm
  rw [hfun]
  exact hrelative

/-- Uniform sampled decay of squared traceless Ricci and an eventual sampled
scalar floor produce the reduced Hamilton limit payload from a compact
realized range of the absolute energy pair.

No quotient, scalar-positivity track, or maximum-principle regularity enters
this compact limit argument. -/
theorem hamiltonConvergencePinchedLimit3Core_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_realized_energyPair_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (t0 + sample i)).tracelessRicciNormSqAt x < epsilon)
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    (C : Set (ℝ × ℝ))
    (hCCompact : IsCompact C)
    (hPairMem : ∀ i : ℕ,
      closedMetricScalarMinimumTracelessRicciMaximumPair
          (gt (t0 + sample i)) ∈ C)
    (hRealized : C ⊆ Set.range
      (fun g : ClosedSmoothRiemannianMetric 3 M ↦
        closedMetricScalarMinimumTracelessRicciMaximumPair g)) :
    HamiltonConvergencePinchedLimit3Core M := by
  let pairSequence : ℕ → ℝ × ℝ := fun i ↦
    closedMetricScalarMinimumTracelessRicciMaximumPair
      (gt (t0 + sample i))
  have hMaximumSampleZero : Tendsto
      (fun i ↦ tracelessRicciMaximumAt (gt (t0 + sample i)))
      atTop (nhds 0) :=
    tendsto_tracelessRicciMaximumAt_zero_of_eventually_uniformly_small
      (fun i ↦ gt (t0 + sample i)) hUniformSmall
  obtain ⟨pairLimit, hPairLimitMem, phi, hphi, hPairLimit⟩ :=
    hCCompact.tendsto_subseq
      (fun i ↦ by simpa [pairSequence] using hPairMem i)
  have hMaximumSubsequence : Tendsto
      (fun i ↦ tracelessRicciMaximumAt
        (gt (t0 + sample (phi i)))) atTop (nhds 0) :=
    hMaximumSampleZero.comp hphi.tendsto_atTop
  have hPairSecond :
      Tendsto (fun i ↦ (pairSequence (phi i)).2) atTop
        (nhds pairLimit.2) :=
    (continuous_snd.tendsto pairLimit).comp hPairLimit
  have hPairSecondZero : pairLimit.2 = 0 := by
    apply tendsto_nhds_unique hPairSecond
    simpa [pairSequence,
      closedMetricScalarMinimumTracelessRicciMaximumPair] using
      hMaximumSubsequence
  have hPairFirst :
      Tendsto (fun i ↦ (pairSequence (phi i)).1) atTop
        (nhds pairLimit.1) :=
    (continuous_fst.tendsto pairLimit).comp hPairLimit
  have hSampleNonneg : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hSampleAtTop.eventually (eventually_ge_atTop (0 : ℝ))
  have hPairFirstLower : c ≤ pairLimit.1 := by
    apply ge_of_tendsto hPairFirst
    filter_upwards
      [hphi.tendsto_atTop.eventually hSampleNonneg,
        hphi.tendsto_atTop.eventually hScalarLower]
      with i hi hLower
    simpa [pairSequence,
      closedMetricScalarMinimumTracelessRicciMaximumPair] using
      le_scalarMinimumAt_of_forall_le_scalarAt
        (gt (t0 + sample (phi i))) (hLower hi)
  obtain ⟨gLimit, hPairEq⟩ := hRealized hPairLimitMem
  have hLimitMinimumLower : c ≤ scalarMinimumAt gLimit := by
    calc
      c ≤ pairLimit.1 := hPairFirstLower
      _ =
          (closedMetricScalarMinimumTracelessRicciMaximumPair gLimit).1 :=
        (congrArg Prod.fst hPairEq).symm
      _ = scalarMinimumAt gLimit := rfl
  have hLimitScalarLower : ∀ x : M, c ≤ gLimit.scalarAt x := by
    intro x
    exact hLimitMinimumLower.trans
      (scalarMinimumAt_le_scalarAt_of_continuous gLimit x)
  have hLimitMaximumZero : tracelessRicciMaximumAt gLimit = 0 := by
    calc
      tracelessRicciMaximumAt gLimit =
          (closedMetricScalarMinimumTracelessRicciMaximumPair gLimit).2 := rfl
      _ = pairLimit.2 := congrArg Prod.snd hPairEq
      _ = 0 := hPairSecondZero
  have hLimitTraceless : ∀ x : M,
      gLimit.tracelessRicciNormSqAt x = 0 := by
    intro x
    apply le_antisymm
    · have hx :=
        tracelessRicciNormSqAt_le_tracelessRicciMaximumAt gLimit x
      simpa only [hLimitMaximumZero] using hx
    · exact gLimit.tracelessRicciNormSqAt_nonneg x (by norm_num)
  obtain ⟨x0⟩ : Nonempty M := inferInstance
  exact ⟨gLimit, hLimitTraceless,
    ⟨x0, hc.trans_le (hLimitScalarLower x0)⟩⟩

/-- The compact realized absolute-energy-pair interface directly yields a
positive Einstein metric. -/
theorem positiveEinsteinMetric3_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_realized_energyPair_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (t0 + sample i)).tracelessRicciNormSqAt x < epsilon)
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    (C : Set (ℝ × ℝ))
    (hCCompact : IsCompact C)
    (hPairMem : ∀ i : ℕ,
      closedMetricScalarMinimumTracelessRicciMaximumPair
          (gt (t0 + sample i)) ∈ C)
    (hRealized : C ⊆ Set.range
      (fun g : ClosedSmoothRiemannianMetric 3 M ↦
        closedMetricScalarMinimumTracelessRicciMaximumPair g)) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_realized_energyPair_range
      gt sample hSampleAtTop hc hUniformSmall hScalarLower C hCCompact
        hPairMem hRealized

/-- A compact parameter space with continuous scalar-minimum / absolute
traceless-energy-maximum pair supplies the compact realized range.  Only the
selected sample must be represented by the compact family. -/
theorem hamiltonConvergencePinchedLimit3Core_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (t0 + sample i)).tracelessRicciNormSqAt x < epsilon)
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℕ → K)
    (hRealize : ∀ i : ℕ,
      metric (parameter i) = gt (t0 + sample i))
    (hInvariantContinuous : Continuous (fun k ↦
      closedMetricScalarMinimumTracelessRicciMaximumPair (metric k))) :
    HamiltonConvergencePinchedLimit3Core M := by
  let C : Set (ℝ × ℝ) := Set.range fun k ↦
    closedMetricScalarMinimumTracelessRicciMaximumPair (metric k)
  have hCCompact : IsCompact C := by
    simpa [C] using isCompact_range hInvariantContinuous
  apply
    hamiltonConvergencePinchedLimit3Core_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_realized_energyPair_range
      gt sample hSampleAtTop hc hUniformSmall hScalarLower C hCCompact
  · intro i
    refine ⟨parameter i, ?_⟩
    change closedMetricScalarMinimumTracelessRicciMaximumPair
      (metric (parameter i)) =
        closedMetricScalarMinimumTracelessRicciMaximumPair
          (gt (t0 + sample i))
    rw [hRealize i]
  · rintro p ⟨k, rfl⟩
    exact ⟨metric k, rfl⟩

/-- The compact-parameterized absolute-energy-pair interface yields a
positive Einstein metric without any quotient hypothesis. -/
theorem positiveEinsteinMetric3_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (t0 + sample i)).tracelessRicciNormSqAt x < epsilon)
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℕ → K)
    (hRealize : ∀ i : ℕ,
      metric (parameter i) = gt (t0 + sample i))
    (hInvariantContinuous : Continuous (fun k ↦
      closedMetricScalarMinimumTracelessRicciMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_parameterization
      gt sample hSampleAtTop hc hUniformSmall hScalarLower metric parameter
        hRealize hInvariantContinuous

/-- Compact realization of the integer-time invariant-pair range gives the
reduced Hamilton limit payload.

This is the exact compactness interface used by the argument: the pair
sequence lies in a compact set of scalar-invariant pairs, and every point of
that compact set is realized by a closed metric.  In particular, no compact
parameterization of metrics, continuity on such a parameter space, or
realization of the full real-time orbit is required. -/
theorem hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt (t0 + s)).scalarAt x)
    (C : Set (ℝ × ℝ))
    (hCCompact : IsCompact C)
    (hPairMem : ∀ i : ℕ,
      closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + (i : ℝ))) ∈ C)
    (hRealized : C ⊆ Set.range
      (fun g : ClosedSmoothRiemannianMetric 3 M ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair g)) :
    HamiltonConvergencePinchedLimit3Core M := by
  let pairSequence : ℕ → ℝ × ℝ := fun i ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair
      (gt (t0 + (i : ℝ)))
  obtain ⟨pairLimit, hPairLimitMem, phi, hphi, hPairLimit⟩ :=
    hCCompact.tendsto_subseq (fun i ↦ by simpa [pairSequence] using hPairMem i)
  have hMaximumSubsequence :
      Tendsto
        (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (phi i : ℝ))
        atTop (nhds 0) :=
    (hMaximumZero.comp tendsto_natCast_atTop_atTop).comp hphi.tendsto_atTop
  have hPairSecond :
      Tendsto (fun i ↦ (pairSequence (phi i)).2) atTop
        (nhds pairLimit.2) :=
    (continuous_snd.tendsto pairLimit).comp hPairLimit
  have hPairSecondZero : pairLimit.2 = 0 := by
    apply tendsto_nhds_unique hPairSecond
    simpa [pairSequence,
      closedMetricScalarMinimumRelativePinchingMaximumPair,
      tracelessPinchingMaximumTrack] using hMaximumSubsequence
  have hPairFirst :
      Tendsto (fun i ↦ (pairSequence (phi i)).1) atTop
        (nhds pairLimit.1) :=
    (continuous_fst.tendsto pairLimit).comp hPairLimit
  have hPairFirstLower : c ≤ pairLimit.1 :=
    ge_of_tendsto hPairFirst <|
      Eventually.of_forall fun i ↦ by
        have hi : (phi i : ℝ) ∈ Ici (0 : ℝ) := by
          simpa only [mem_Ici] using
            (Nat.cast_nonneg (phi i) : (0 : ℝ) ≤ (phi i : ℝ))
        simpa [pairSequence,
          closedMetricScalarMinimumRelativePinchingMaximumPair] using
          le_scalarMinimumAt_of_forall_le_scalarAt
            (gt (t0 + (phi i : ℝ)))
            (hScalarLower (phi i : ℝ) hi)
  obtain ⟨gLimit, hPairEq⟩ := hRealized hPairLimitMem
  have hLimitMinimumLower : c ≤ scalarMinimumAt gLimit := by
    calc
      c ≤ pairLimit.1 := hPairFirstLower
      _ = (closedMetricScalarMinimumRelativePinchingMaximumPair gLimit).1 :=
        (congrArg Prod.fst hPairEq).symm
      _ = scalarMinimumAt gLimit := rfl
  have hLimitScalarLower : ∀ x : M, c ≤ gLimit.scalarAt x := by
    intro x
    exact hLimitMinimumLower.trans
      (scalarMinimumAt_le_scalarAt_of_continuous gLimit x)
  have hLimitMaximumZero :
      tracelessPinchingMaximumAt gLimit 0 = 0 := by
    calc
      tracelessPinchingMaximumAt gLimit 0 =
          (closedMetricScalarMinimumRelativePinchingMaximumPair gLimit).2 := rfl
      _ = pairLimit.2 := congrArg Prod.snd hPairEq
      _ = 0 := hPairSecondZero
  have hLimitTraceless : ∀ x : M,
      gLimit.tracelessRicciNormSqAt x = 0 := by
    intro x
    have hRpos : ∀ y : M, 0 < gLimit.scalarAt y :=
      fun y ↦ hc.trans_le (hLimitScalarLower y)
    have hTQContinuous :
        Continuous (fun y : M ↦ gLimit.tracelessPinchingAt y 0) :=
      continuous_tracelessPinchingAt_zero_of_scalarAt_pos gLimit hRpos
    obtain ⟨xmax, _hxmax, hmax⟩ :=
      isCompact_univ.exists_isMaxOn
        (Set.univ_nonempty)
        (fun y _ ↦ hTQContinuous.continuousAt.continuousWithinAt)
    have hpointLeMaximum :
        gLimit.tracelessPinchingAt x 0 ≤
          tracelessPinchingMaximumAt gLimit 0 := by
      rw [tracelessPinchingMaximumAt_eq_of_isMaxOn
        (g := gLimit) 0 hmax]
      exact hmax trivial
    have hpointLeZero : gLimit.tracelessPinchingAt x 0 ≤ 0 := by
      simpa only [hLimitMaximumZero] using hpointLeMaximum
    have hpointNonneg : 0 ≤ gLimit.tracelessPinchingAt x 0 :=
      gLimit.tracelessPinchingAt_nonneg_of_scalarAt_pos
        x 0 (by norm_num) (hRpos x)
    have hpointZero : gLimit.tracelessPinchingAt x 0 = 0 :=
      le_antisymm hpointLeZero hpointNonneg
    have hquotient :
        gLimit.tracelessRicciNormSqAt x / (gLimit.scalarAt x) ^ 2 = 0 := by
      simpa [ClosedSmoothRiemannianMetric.tracelessPinchingAt,
        Real.rpow_two] using hpointZero
    exact (div_eq_zero_iff.mp hquotient).resolve_right
      (pow_ne_zero 2 (hRpos x).ne')
  obtain ⟨x0⟩ : Nonempty M := inferInstance
  exact ⟨gLimit, hLimitTraceless,
    ⟨x0, hc.trans_le (hLimitScalarLower x0)⟩⟩

/-- A compact realized set containing an arbitrary escaping sample of the two
scalar invariants suffices to realize the reduced Hamilton limit payload.

This is the reusable sampled compactness interface.  Decay of relative
pinching and the positive scalar lower bound are required only along the
sample.  The scalar premise is eventual, so a finite initial part of the
sample is irrelevant.  Every point of the ambient compact set must be
realized by some closed metric, but no convergence of those metrics is
assumed. -/
theorem hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hMaximumSampleZero :
      Tendsto
        (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (sample i))
        atTop (nhds 0))
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    (C : Set (ℝ × ℝ))
    (hCCompact : IsCompact C)
    (hPairMem : ∀ i : ℕ,
      closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + sample i)) ∈ C)
    (hRealized : C ⊆ Set.range
      (fun g : ClosedSmoothRiemannianMetric 3 M ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair g)) :
    HamiltonConvergencePinchedLimit3Core M := by
  let pairSequence : ℕ → ℝ × ℝ := fun i ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair
      (gt (t0 + sample i))
  obtain ⟨pairLimit, hPairLimitMem, phi, hphi, hPairLimit⟩ :=
    hCCompact.tendsto_subseq
      (fun i ↦ by simpa [pairSequence] using hPairMem i)
  have hMaximumSubsequence :
      Tendsto
        (fun i ↦
          tracelessPinchingMaximumTrack gt t0 0 (sample (phi i)))
        atTop (nhds 0) :=
    hMaximumSampleZero.comp hphi.tendsto_atTop
  have hPairSecond :
      Tendsto (fun i ↦ (pairSequence (phi i)).2) atTop
        (nhds pairLimit.2) :=
    (continuous_snd.tendsto pairLimit).comp hPairLimit
  have hPairSecondZero : pairLimit.2 = 0 := by
    apply tendsto_nhds_unique hPairSecond
    simpa [pairSequence,
      closedMetricScalarMinimumRelativePinchingMaximumPair,
      tracelessPinchingMaximumTrack] using hMaximumSubsequence
  have hPairFirst :
      Tendsto (fun i ↦ (pairSequence (phi i)).1) atTop
        (nhds pairLimit.1) :=
    (continuous_fst.tendsto pairLimit).comp hPairLimit
  have hSampleNonneg : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hSampleAtTop.eventually (eventually_ge_atTop (0 : ℝ))
  have hPairFirstLower : c ≤ pairLimit.1 := by
    apply ge_of_tendsto hPairFirst
    filter_upwards
      [hphi.tendsto_atTop.eventually hSampleNonneg,
        hphi.tendsto_atTop.eventually hScalarLower]
      with i hi hLower
    simpa [pairSequence,
      closedMetricScalarMinimumRelativePinchingMaximumPair] using
      le_scalarMinimumAt_of_forall_le_scalarAt
        (gt (t0 + sample (phi i))) (hLower hi)
  obtain ⟨gLimit, hPairEq⟩ := hRealized hPairLimitMem
  have hLimitMinimumLower : c ≤ scalarMinimumAt gLimit := by
    calc
      c ≤ pairLimit.1 := hPairFirstLower
      _ = (closedMetricScalarMinimumRelativePinchingMaximumPair gLimit).1 :=
        (congrArg Prod.fst hPairEq).symm
      _ = scalarMinimumAt gLimit := rfl
  have hLimitScalarLower : ∀ x : M, c ≤ gLimit.scalarAt x := by
    intro x
    exact hLimitMinimumLower.trans
      (scalarMinimumAt_le_scalarAt_of_continuous gLimit x)
  have hLimitMaximumZero :
      tracelessPinchingMaximumAt gLimit 0 = 0 := by
    calc
      tracelessPinchingMaximumAt gLimit 0 =
          (closedMetricScalarMinimumRelativePinchingMaximumPair gLimit).2 := rfl
      _ = pairLimit.2 := congrArg Prod.snd hPairEq
      _ = 0 := hPairSecondZero
  have hLimitTraceless : ∀ x : M,
      gLimit.tracelessRicciNormSqAt x = 0 := by
    intro x
    have hRpos : ∀ y : M, 0 < gLimit.scalarAt y :=
      fun y ↦ hc.trans_le (hLimitScalarLower y)
    have hTQContinuous :
        Continuous (fun y : M ↦ gLimit.tracelessPinchingAt y 0) :=
      continuous_tracelessPinchingAt_zero_of_scalarAt_pos gLimit hRpos
    obtain ⟨xmax, _hxmax, hmax⟩ :=
      isCompact_univ.exists_isMaxOn
        (Set.univ_nonempty)
        (fun y _ ↦ hTQContinuous.continuousAt.continuousWithinAt)
    have hpointLeMaximum :
        gLimit.tracelessPinchingAt x 0 ≤
          tracelessPinchingMaximumAt gLimit 0 := by
      rw [tracelessPinchingMaximumAt_eq_of_isMaxOn
        (g := gLimit) 0 hmax]
      exact hmax trivial
    have hpointLeZero : gLimit.tracelessPinchingAt x 0 ≤ 0 := by
      simpa only [hLimitMaximumZero] using hpointLeMaximum
    have hpointNonneg : 0 ≤ gLimit.tracelessPinchingAt x 0 :=
      gLimit.tracelessPinchingAt_nonneg_of_scalarAt_pos
        x 0 (by norm_num) (hRpos x)
    have hpointZero : gLimit.tracelessPinchingAt x 0 = 0 :=
      le_antisymm hpointLeZero hpointNonneg
    have hquotient :
        gLimit.tracelessRicciNormSqAt x / (gLimit.scalarAt x) ^ 2 = 0 := by
      simpa [ClosedSmoothRiemannianMetric.tracelessPinchingAt,
        Real.rpow_two] using hpointZero
    exact (div_eq_zero_iff.mp hquotient).resolve_right
      (pow_ne_zero 2 (hRpos x).ne')
  obtain ⟨x0⟩ : Nonempty M := inferInstance
  exact ⟨gLimit, hLimitTraceless,
    ⟨x0, hc.trans_le (hLimitScalarLower x0)⟩⟩

/-- An arbitrary escaping forward sample of the two scalar invariants suffices
to realize the reduced Hamilton limit payload.

Unlike the integer-time compatibility theorem below, scalar positivity is
required only at the sampled slices.  Compactness is likewise imposed only on
the sampled invariant-pair range.  Since every point of that range is the pair
of the corresponding sampled metric, the range realizes its own cluster
point; no compact metric parameter space is needed. -/
theorem hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_invariantPair_sample_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hSampleNonneg : ∀ i : ℕ, 0 ≤ sample i)
    (hc : 0 < c)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hScalarLower : ∀ i : ℕ, 0 ≤ sample i → ∀ x : M,
      c ≤ (gt (t0 + sample i)).scalarAt x)
    (hPairRangeCompact : IsCompact
      (Set.range (fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + sample i))))) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
      gt sample hSampleAtTop hc (hMaximumZero.comp hSampleAtTop)
        (Eventually.of_forall fun i _hi ↦
          hScalarLower i (hSampleNonneg i))
        (Set.range (fun i : ℕ ↦
          closedMetricScalarMinimumRelativePinchingMaximumPair
            (gt (t0 + sample i)))) hPairRangeCompact
  · exact fun i ↦ Set.mem_range_self i
  · rintro p ⟨i, rfl⟩
    exact ⟨gt (t0 + sample i), rfl⟩

/-- A compact parameter space with a continuous invariant-pair map supplies
the reusable sampled realized-set interface.  The parameter map and metric
realization are required only on the selected sample, not on the full forward
orbit. -/
theorem hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hMaximumSampleZero :
      Tendsto
        (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (sample i))
        atTop (nhds 0))
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℕ → K)
    (hRealize : ∀ i : ℕ,
      metric (parameter i) = gt (t0 + sample i))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    HamiltonConvergencePinchedLimit3Core M := by
  let C : Set (ℝ × ℝ) := Set.range fun k ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)
  have hCCompact : IsCompact C := by
    simpa [C] using isCompact_range hInvariantContinuous
  apply
    hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
      gt sample hSampleAtTop hc hMaximumSampleZero hScalarLower C hCCompact
  · intro i
    refine ⟨parameter i, ?_⟩
    change closedMetricScalarMinimumRelativePinchingMaximumPair
      (metric (parameter i)) =
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + sample i))
    rw [hRealize i]
  · rintro p ⟨k, rfl⟩
    exact ⟨metric k, rfl⟩

/-- Compactness of the actual metric-orbit closure supplies the sampled
realized invariant set directly as its invariant-pair image.

This removes the auxiliary compact type, metric map, and parameter map from
the sampled compactness interface.  The remaining hypotheses are precisely
the metric-orbit precompactness boundary and continuity of the two consumed
invariants on that closure. -/
theorem hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_metricOrbitClosure
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hMaximumSampleZero :
      Tendsto
        (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (sample i))
        atTop (nhds 0))
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous :
      ContinuousOn
        (closedMetricScalarMinimumRelativePinchingMaximumPair (M := M))
        (closure (Set.range gt))) :
    HamiltonConvergencePinchedLimit3Core M := by
  let C : Set (ℝ × ℝ) :=
    closedMetricScalarMinimumRelativePinchingMaximumPair ''
      closure (Set.range gt)
  have hCCompact : IsCompact C := by
    simpa only [C] using
      hOrbitCompact.image_of_continuousOn hInvariantContinuous
  apply
    hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
      gt sample hSampleAtTop hc hMaximumSampleZero hScalarLower C hCCompact
  · intro i
    exact ⟨gt (t0 + sample i),
      subset_closure ⟨t0 + sample i, rfl⟩, rfl⟩
  · rintro p ⟨g, _hg, rfl⟩
    exact ⟨g, rfl⟩

/-- Compactness of the literal integer-time invariant-pair range is a
self-realizing special case of the compact realized-range interface.

Every member of this range is, by construction, the invariant pair of the
corresponding flow metric.  Thus the compactness of this scalar pair range is
the only compactness input. -/
theorem hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_invariantPair_sequence_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt (t0 + s)).scalarAt x)
    (hPairRangeCompact : IsCompact
      (Set.range (fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + (i : ℝ)))))) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
      gt hc hMaximumZero hScalarLower
        (Set.range (fun i : ℕ ↦
          closedMetricScalarMinimumRelativePinchingMaximumPair
            (gt (t0 + (i : ℝ)))))
        hPairRangeCompact
  · exact fun i ↦ Set.mem_range_self i
  · rintro p ⟨i, rfl⟩
    exact ⟨gt (t0 + (i : ℝ)), rfl⟩

/-- Compact realization of a positive scalar-minimum and a vanishing
relative-pinching maximum gives the reduced Hamilton limit payload.

The compact parameterization is a convenient sufficient condition for the
weaker compact realized invariant-pair range interface above.  This theorem is
kept as the parameterized compatibility wrapper. -/
theorem hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt (t0 + s)).scalarAt x)
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ s ∈ Ici (0 : ℝ),
      metric (parameter s) = gt (t0 + s))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    HamiltonConvergencePinchedLimit3Core M := by
  let C : Set (ℝ × ℝ) := Set.range fun k ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)
  have hCCompact : IsCompact C := by
    simpa [C] using isCompact_range hInvariantContinuous
  apply
    hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
      gt hc hMaximumZero hScalarLower C hCCompact
  · intro i
    refine ⟨parameter (i : ℝ), ?_⟩
    change closedMetricScalarMinimumRelativePinchingMaximumPair
      (metric (parameter (i : ℝ))) =
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + (i : ℝ)))
    have hi : (i : ℝ) ∈ Ici (0 : ℝ) := by
      simpa only [mem_Ici] using
        (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))
    rw [hRealize (i : ℝ) hi]
  · rintro p ⟨k, rfl⟩
    exact ⟨metric k, rfl⟩

/-- Sampled relative-pinching decay and eventual sampled scalar positivity
produce a positive Einstein metric from any compact realized set containing
the sampled invariant pairs. -/
theorem positiveEinsteinMetric3_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hMaximumSampleZero :
      Tendsto
        (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (sample i))
        atTop (nhds 0))
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    (C : Set (ℝ × ℝ))
    (hCCompact : IsCompact C)
    (hPairMem : ∀ i : ℕ,
      closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + sample i)) ∈ C)
    (hRealized : C ⊆ Set.range
      (fun g : ClosedSmoothRiemannianMetric 3 M ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair g)) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_realized_invariantPair_range
      gt sample hSampleAtTop hc hMaximumSampleZero hScalarLower C hCCompact
        hPairMem hRealized

/-- The sampled compact-parameterization interface directly yields a positive
Einstein metric.  Only the selected sample must be represented by the compact
family. -/
theorem positiveEinsteinMetric3_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hMaximumSampleZero :
      Tendsto
        (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (sample i))
        atTop (nhds 0))
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℕ → K)
    (hRealize : ∀ i : ℕ,
      metric (parameter i) = gt (t0 + sample i))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
      gt sample hSampleAtTop hc hMaximumSampleZero hScalarLower metric
        parameter hRealize hInvariantContinuous

/-- The compact closure of the actual metric orbit and continuity of the two
sampled invariants on it realize the positive Einstein limit. -/
theorem positiveEinsteinMetric3_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_metricOrbitClosure
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hc : 0 < c)
    (hMaximumSampleZero :
      Tendsto
        (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (sample i))
        atTop (nhds 0))
    (hScalarLower : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c ≤ (gt (t0 + sample i)).scalarAt x)
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous :
      ContinuousOn
        (closedMetricScalarMinimumRelativePinchingMaximumPair (M := M))
        (closure (Set.range gt))) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_metricOrbitClosure
      gt sample hSampleAtTop hc hMaximumSampleZero hScalarLower hOrbitCompact
        hInvariantContinuous

/-- Compactness of the integer-time invariant-pair range, together with
positive scalar control and decay of relative pinching, directly produces a
positive Einstein metric. -/
theorem positiveEinsteinMetric3_of_relativePinchingMaximum_tendsto_zero_of_compact_invariantPair_sequence_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt (t0 + s)).scalarAt x)
    (hPairRangeCompact : IsCompact
      (Set.range (fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + (i : ℝ)))))) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_invariantPair_sequence_range
      gt hc hMaximumZero hScalarLower hPairRangeCompact

/-- Decay of relative pinching and scalar positivity only along an arbitrary
escaping forward sample produce a positive Einstein metric when the sampled
invariant-pair range is compact. -/
theorem positiveEinsteinMetric3_of_relativePinchingMaximum_tendsto_zero_of_compact_invariantPair_sample_range
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hSampleNonneg : ∀ i : ℕ, 0 ≤ sample i)
    (hc : 0 < c)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hScalarLower : ∀ i : ℕ, 0 ≤ sample i → ∀ x : M,
      c ≤ (gt (t0 + sample i)).scalarAt x)
    (hPairRangeCompact : IsCompact
      (Set.range (fun i : ℕ ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair
          (gt (t0 + sample i))))) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_invariantPair_sample_range
      gt sample hSampleAtTop hSampleNonneg hc hMaximumZero hScalarLower
        hPairRangeCompact

/-- The preceding compact realization theorem yields an actual positive
Einstein metric, using the already-proved equivalence with the reduced
Hamilton limit payload. -/
theorem positiveEinsteinMetric3_of_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt (t0 + s)).scalarAt x)
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ s ∈ Ici (0 : ℝ),
      metric (parameter s) = gt (t0 + s))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
      gt hc hMaximumZero hScalarLower metric parameter hRealize
        hInvariantContinuous

/-- Fully analytic-to-compact endpoint at Hamilton's transported `R / 6`
floor.

Explicit improved-pinching evolution on every translated forward slab makes
the exponent-zero maximum antitone. Integrability then forces its decay, and
the compact two-invariant realization produces a positive Einstein metric.
The only remaining limit input is continuity of that invariant pair on a
compact parameter space containing the forward orbit. -/
theorem positiveEinsteinMetric3_of_hamilton_one_sixth_forward_improvement_of_integrableMaximum_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt (t0 + s)).scalarAt x)
    (hQCont : ∀ s ∈ Ici (0 : ℝ),
      Continuous ↿(fun tau (x : M) ↦
        (gt ((t0 + s) + tau)).tracelessPinchingAt x 0))
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hEvol : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + s) x 0
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hPin : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) (1 / 6))
    (hIntegrable :
      IntegrableOn (tracelessPinchingMaximumTrack gt t0 0) (Ici 0))
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ s ∈ Ici (0 : ℝ),
      metric (parameter s) = gt (t0 + s))
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  have hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 0) (Ici (0 : ℝ)) :=
    tracelessPinchingMaximumTrack_antitoneOn_of_hamilton_forward_improvement
      (gt := gt) (t0 := t0) (epsilon := (1 / 6 : ℝ)) (delta := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [PinchingAlgebra.pinchedTracelessAdmissibleDelta3])
      hQCont hQTwo hEvol hPin
  have hRpos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x :=
    fun s hs x ↦ hc.trans_le (hScalarLower s hs x)
  have hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) :=
    tracelessPinchingMaximumTrack_tendsto_zero_of_antitoneOn_of_integrableOn
      gt hRpos hQTwo hAntitone hIntegrable
  exact
    positiveEinsteinMetric3_of_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
      gt hc hMaximumZero hScalarLower metric parameter hRealize
        hInvariantContinuous

end Poincare
