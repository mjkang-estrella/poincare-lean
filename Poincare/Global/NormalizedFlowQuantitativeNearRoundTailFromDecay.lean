import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureQuantitativeNearRoundTail
import Poincare.Global.NormalizedFlowPinchingLimit

/-!
# Producing the quantitative near-round tail from asymptotic decay

The quantitative Hamilton package needs two geometric facts after one finite
time: every Ricci eigenvalue is at least `3 / 10` of the scalar curvature, and
the pointwise scalar curvature is at most `3 / 2` times its spatial mean.

This file derives both from exact uniform `atTop` contracts.  Uniform decay of
the exponent-zero improved-pinching maximum supplies the first contract.
Uniform relative decay of `R - mean R`, together with a positive mean floor,
supplies positivity and the second estimate.  The two eventual statements are
synchronized into a single nonnegative physical tail start, so the conclusion
can be inserted directly into
`NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3`
and its decay wrapper.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

namespace PinchingAlgebra

/-- If the squared traceless part is less than `(R / 30)^2`, every diagonal
Ricci eigenvalue is strictly larger than `(3 / 10) R`. -/
theorem diagonal_eigenvalue_three_tenths_floor_of_scalar_pos_of_traceless_lt
    {a b c : ℝ}
    (hscalar : 0 < diagonalScalar3 a b c)
    (htraceless :
      diagonalTracelessRicciNormSq3 a b c <
        (diagonalScalar3 a b c / 30) ^ 2) :
    (3 / 10 : ℝ) * diagonalScalar3 a b c < a ∧
      (3 / 10 : ℝ) * diagonalScalar3 a b c < b ∧
        (3 / 10 : ℝ) * diagonalScalar3 a b c < c := by
  let R : ℝ := diagonalScalar3 a b c
  have hR : 0 < R := by simpa only [R] using hscalar
  have hdecomp :
      diagonalTracelessRicciNormSq3 a b c =
        (a - R / 3) ^ 2 + (b - R / 3) ^ 2 + (c - R / 3) ^ 2 := by
    simp [R, diagonalTracelessRicciNormSq3, diagonalRicciNormSq3,
      diagonalScalar3]
    ring
  have hsmall :
      (a - R / 3) ^ 2 + (b - R / 3) ^ 2 + (c - R / 3) ^ 2 <
        (R / 30) ^ 2 := by
    simpa only [hdecomp, R] using htraceless
  have lower_of_component
      {x y z : ℝ}
      (hsum :
        (x - R / 3) ^ 2 + (y - R / 3) ^ 2 + (z - R / 3) ^ 2 <
          (R / 30) ^ 2) :
      (3 / 10 : ℝ) * R < x := by
    have hy : 0 ≤ (y - R / 3) ^ 2 := sq_nonneg _
    have hz : 0 ≤ (z - R / 3) ^ 2 := sq_nonneg _
    have hxdev : (x - R / 3) ^ 2 < (R / 30) ^ 2 := by
      nlinarith
    by_contra hnot
    have hxle : x ≤ (3 / 10 : ℝ) * R := le_of_not_gt hnot
    have hfirst : 0 ≤ R / 3 - x - R / 30 := by
      nlinarith
    have hsecond : 0 ≤ R / 3 - x + R / 30 := by
      nlinarith
    have hprod :
        0 ≤ (R / 3 - x - R / 30) * (R / 3 - x + R / 30) :=
      mul_nonneg hfirst hsecond
    nlinarith [hprod]
  refine ⟨lower_of_component hsmall, ?_, ?_⟩
  · apply lower_of_component (x := b) (y := a) (z := c)
    nlinarith [hsmall]
  · apply lower_of_component (x := c) (y := a) (z := b)
    nlinarith [hsmall]

end PinchingAlgebra

section PointwiseFloor

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "TM" => (TangentSpace I : M → Type _)

/-- Relative squared-traceless-Ricci anisotropy below `1 / 900` forces the
global `3 / 10` Ricci-eigenvalue floor. -/
theorem
    ClosedSmoothRiemannianMetric.globalRicciEigenvalueFloor_three_tenths_of_scalar_pos_of_relativeTracelessRicci_lt
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hRpos : ∀ x : M, 0 < g.scalarAt x)
    (hRelative : ∀ x : M,
      g.relativeTracelessRicciAt x < (1 / 900 : ℝ)) :
    GlobalRicciEigenvalueFloor3 g (3 / 10) := by
  intro x b mu hEig i
  have hR :
      g.scalarAt x =
        PinchingAlgebra.diagonalScalar3 (mu 0) (mu 1) (mu 2) := by
    rw [g.scalarAt_eq_sum_eigenvalues_of_ricciEndoAt_eigenbasis b mu hEig]
    simp [Fin.sum_univ_three, PinchingAlgebra.diagonalScalar3]
  have hT :
      g.tracelessRicciNormSqAt x =
        PinchingAlgebra.diagonalTracelessRicciNormSq3
          (mu 0) (mu 1) (mu 2) :=
    g.tracelessRicciNormSqAt_eq_diagonal_of_ricciEndoAt_eigenbasis
      rfl b mu hEig
  have hR2 : 0 < (g.scalarAt x) ^ 2 := sq_pos_of_pos (hRpos x)
  have hRelative' :
      g.tracelessRicciNormSqAt x / (g.scalarAt x) ^ 2 <
        (1 / 900 : ℝ) := by
    simpa only [g.relativeTracelessRicciAt_eq] using hRelative x
  have hAbsolute :
      g.tracelessRicciNormSqAt x < (g.scalarAt x / 30) ^ 2 := by
    have hMul := (div_lt_iff₀ hR2).1 hRelative'
    calc
      g.tracelessRicciNormSqAt x < (1 / 900 : ℝ) * (g.scalarAt x) ^ 2 :=
        hMul
      _ = (g.scalarAt x / 30) ^ 2 := by ring
  have hfloor :=
    PinchingAlgebra.diagonal_eigenvalue_three_tenths_floor_of_scalar_pos_of_traceless_lt
      (a := mu 0) (b := mu 1) (c := mu 2)
      (by simpa only [← hR] using hRpos x)
      (by simpa only [← hR, ← hT] using hAbsolute)
  have hi : (3 / 10 : ℝ) * g.scalarAt x < mu i := by
    fin_cases i
    · simpa only [hR] using hfloor.1
    · simpa only [hR] using hfloor.2.1
    · simpa only [hR] using hfloor.2.2
  exact hi.le

end PointwiseFloor

section UniformDecayContracts

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/-- Exact uniform scale-invariant traceless-Ricci decay on a translated
forward ray. -/
def UniformRelativeTracelessRicciDecayAtTop3
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t0 : ℝ)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∀ eta : ℝ, 0 < eta → ∀ᶠ s in atTop, ∀ x : M,
    (gt (t0 + s)).relativeTracelessRicciAt x < eta

/-- Exact uniform relative scalar-to-mean oscillation decay on a translated
forward ray. -/
def UniformRelativeScalarMeanOscillationDecayAtTop3
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t0 : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∀ᶠ s in atTop, ∀ x : M,
    |(gt (t0 + s)).scalarAt x - meanScalar (gt (t0 + s))| <
      eta * meanScalar (gt (t0 + s))

/-- Decay of the existing exponent-zero spatial maximum is exactly enough to
produce uniform relative traceless-Ricci decay. -/
theorem uniformRelativeTracelessRicciDecayAtTop3_of_tracelessPinchingMaximumTrack_tendsto_zero
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) {t0 : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0)) :
    UniformRelativeTracelessRicciDecayAtTop3 gt t0 := by
  intro eta heta
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    hMaximumZero.eventually (Iio_mem_nhds heta)] with s hs hmax
  intro x
  rw [(gt (t0 + s)).relativeTracelessRicciAt_eq_tracelessPinchingAt_zero]
  exact
    (tracelessPinchingAt_le_tracelessPinchingMaximumTrack
      gt t0 0 s (hQTwo s hs) x).trans_lt hmax

omit [SecondCountableTopology M] in
/-- A positive mean floor and relative scalar oscillation below `1 / 2`
eventually give both positive scalar curvature and `R ≤ (3/2) mean R`. -/
theorem eventually_scalarPositive_and_le_three_halves_mul_meanScalar_of_relativeScalarMeanOscillationDecay
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) {t0 rho : ℝ}
    (hrho : 0 < rho)
    (hMeanLower : ∀ s ∈ Ici (0 : ℝ),
      rho ≤ meanScalar (gt (t0 + s)))
    (hOscillation :
      UniformRelativeScalarMeanOscillationDecayAtTop3 gt t0) :
    ∀ᶠ s in atTop,
      (∀ x : M, 0 < (gt (t0 + s)).scalarAt x) ∧
      (∀ x : M,
        (gt (t0 + s)).scalarAt x ≤
          (3 / 2 : ℝ) * meanScalar (gt (t0 + s))) := by
  have hHalf := hOscillation (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop (0 : ℝ), hHalf]
    with s hs hosc
  have hMeanPos : 0 < meanScalar (gt (t0 + s)) :=
    hrho.trans_le (hMeanLower s hs)
  constructor
  · intro x
    have hLower := neg_abs_le
      ((gt (t0 + s)).scalarAt x - meanScalar (gt (t0 + s)))
    have hx := hosc x
    nlinarith
  · intro x
    have hUpper := le_abs_self
      ((gt (t0 + s)).scalarAt x - meanScalar (gt (t0 + s)))
    have hx := hosc x
    nlinarith

omit [SecondCountableTopology M] in
/-- The two exact uniform decay contracts synchronize after one nonnegative
relative time.  The traceless threshold `1/900` yields the `3/10`
Ricci-eigenvalue floor, while scalar oscillation below `1/2` yields the
`3/2` scalar-to-mean comparison. -/
theorem exists_quantitativeNearRoundTail_of_uniformRelativeDecay
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) {t0 rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (ht0 : 0 ≤ t0) (hrho : 0 < rho)
    (hMeanLower : ∀ s ∈ Ici (0 : ℝ),
      rho ≤ meanScalar (gt (t0 + s)))
    (hTraceless : UniformRelativeTracelessRicciDecayAtTop3 gt t0)
    (hOscillation :
      UniformRelativeScalarMeanOscillationDecayAtTop3 gt t0) :
    ∃ T : ℝ, 0 ≤ T ∧ t0 ≤ T ∧
      (∀ t ∈ Ici T, ∀ x : M, 0 < (gt t).scalarAt x) ∧
      (∀ t ∈ Ici T,
        GlobalRicciEigenvalueFloor3 (gt t)
          quantitativeNearRoundPinchingEpsilon3) ∧
      (∀ t ∈ Ici T, ∀ x : M,
        (gt t).scalarAt x ≤ (3 / 2 : ℝ) * meanScalar (gt t)) := by
  have hScalarTail :=
    eventually_scalarPositive_and_le_three_halves_mul_meanScalar_of_relativeScalarMeanOscillationDecay
      gt hrho hMeanLower hOscillation
  have hTracelessTail := hTraceless (1 / 900) (by norm_num)
  have hCombined : ∀ᶠ s in atTop,
      0 ≤ s ∧
      (∀ x : M, 0 < (gt (t0 + s)).scalarAt x) ∧
      GlobalRicciEigenvalueFloor3 (gt (t0 + s))
        quantitativeNearRoundPinchingEpsilon3 ∧
      (∀ x : M,
        (gt (t0 + s)).scalarAt x ≤
          (3 / 2 : ℝ) * meanScalar (gt (t0 + s))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hScalarTail,
      hTracelessTail] with s hs hScalar hRelative
    refine ⟨hs, hScalar.1, ?_, hScalar.2⟩
    simpa only [quantitativeNearRoundPinchingEpsilon3] using
      (gt (t0 + s)).globalRicciEigenvalueFloor_three_tenths_of_scalar_pos_of_relativeTracelessRicci_lt
        hScalar.1 hRelative
  obtain ⟨S, hS⟩ := eventually_atTop.1 hCombined
  have hS0 : 0 ≤ S := (hS S le_rfl).1
  refine ⟨t0 + S, add_nonneg ht0 hS0, le_add_of_nonneg_right hS0,
    ?_, ?_, ?_⟩
  · intro t ht x
    have hs : S ≤ t - t0 := by
      have ht' : t0 + S ≤ t := ht
      linarith
    have htail := hS (t - t0) hs
    have htime : t0 + (t - t0) = t := by ring
    simpa only [htime] using htail.2.1 x
  · intro t ht
    have hs : S ≤ t - t0 := by
      have ht' : t0 + S ≤ t := ht
      linarith
    have htail := hS (t - t0) hs
    have htime : t0 + (t - t0) = t := by ring
    simpa only [htime] using htail.2.2.1
  · intro t ht x
    have hs : S ≤ t - t0 := by
      have ht' : t0 + S ≤ t := ht
      linarith
    have htail := hS (t - t0) hs
    have htime : t0 + (t - t0) = t := by ring
    simpa only [htime] using htail.2.2.2 x

/-- Direct bridge from the existing improved-pinching maximum limit to the
synchronized quantitative near-round tail. -/
theorem exists_quantitativeNearRoundTail_of_tracelessPinchingMaximumTrack_tendsto_zero_of_relativeScalarMeanOscillationDecay
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) {t0 rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (ht0 : 0 ≤ t0) (hrho : 0 < rho)
    (hMeanLower : ∀ s ∈ Ici (0 : ℝ),
      rho ≤ meanScalar (gt (t0 + s)))
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hMaximumZero :
      Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0))
    (hOscillation :
      UniformRelativeScalarMeanOscillationDecayAtTop3 gt t0) :
    ∃ T : ℝ, 0 ≤ T ∧ t0 ≤ T ∧
      (∀ t ∈ Ici T, ∀ x : M, 0 < (gt t).scalarAt x) ∧
      (∀ t ∈ Ici T,
        GlobalRicciEigenvalueFloor3 (gt t)
          quantitativeNearRoundPinchingEpsilon3) ∧
      (∀ t ∈ Ici T, ∀ x : M,
        (gt t).scalarAt x ≤ (3 / 2 : ℝ) * meanScalar (gt t)) :=
  exists_quantitativeNearRoundTail_of_uniformRelativeDecay
    gt ht0 hrho hMeanLower
      (uniformRelativeTracelessRicciDecayAtTop3_of_tracelessPinchingMaximumTrack_tendsto_zero
        gt hQTwo hMaximumZero)
      hOscillation

end UniformDecayContracts

/-!
## Compact-flow package constructor
-/

/-- The compact normalized-flow fields which do not depend on choosing the
near-round tail start.  The constructor below combines this base with the two
uniform decay contracts and selects the common tail internally. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundCompactFlowBaseData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : Ici (0 : ℝ) → K
  parameterContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous parameter
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  meanScalarFloor : ℝ
  meanScalarFloor_pos : 0 < meanScalarFloor
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  normalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  compactFiniteAtlasChartFrameDensityData :
    CompactFiniteAtlasChartFrameDensityData gt
  jointMetricEntries : ∀ t : ℝ, ∀ x : M,
    MetricEntriesJointContDiffAt gt t x 3
  finiteVolumeMeasureContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k))
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)

namespace NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundCompactFlowBaseData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Compact base data plus the two exact uniform decay contracts construct an
actual quantitative near-round decay package.  The common tail start is
chosen inside the proof and is not an input field. -/
theorem nonempty_quantitativeNearRoundTailDecayAnalyticData3_of_uniformRelativeDecay
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundCompactFlowBaseData3.{u, v}
        M)
    {t0 rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1]
    (ht0 : 0 ≤ t0) (hrho : 0 < rho)
    (hMeanLower : ∀ s ∈ Ici (0 : ℝ),
      rho ≤ meanScalar (data.gt (t0 + s)))
    (hTraceless : UniformRelativeTracelessRicciDecayAtTop3 data.gt t0)
    (hOscillation :
      UniformRelativeScalarMeanOscillationDecayAtTop3 data.gt t0) :
    Nonempty
      (NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
        M) := by
  obtain ⟨T, hT0, _ht0T, hScalarPositive, hEigenFloor,
      hScalarMean⟩ :=
    exists_quantitativeNearRoundTail_of_uniformRelativeDecay
      data.gt ht0 hrho hMeanLower hTraceless hOscillation
  let nearRound :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailCoreData3.{u, v}
        M :=
    { K := data.K
      topologicalSpaceK := data.topologicalSpaceK
      compactSpaceK := data.compactSpaceK
      gt := data.gt
      metric := data.metric
      parameter := data.parameter
      parameterContinuous := data.parameterContinuous
      realizesFlow := data.realizesFlow
      meanScalarFloor := data.meanScalarFloor
      meanScalarFloor_pos := data.meanScalarFloor_pos
      meanScalarLower := data.meanScalarLower
      normalizedFlow := data.normalizedFlow
      compactFiniteAtlasChartFrameDensityData :=
        data.compactFiniteAtlasChartFrameDensityData
      jointMetricEntries := data.jointMetricEntries
      tailStart := T
      tailStart_nonneg := hT0
      scalarPositiveOnTail := hScalarPositive
      ricciEigenvalueFloorOnTail := hEigenFloor
      finiteVolumeMeasureContinuous := data.finiteVolumeMeasureContinuous
      scalarJointContinuous := data.scalarJointContinuous
      tracelessRicciNormSqJointContinuous :=
        data.tracelessRicciNormSqJointContinuous }
  exact ⟨
    { nearRound := nearRound
      scalarAt_le_three_halves_mul_meanScalarOnTail := hScalarMean }⟩

/-- Convenience form using the compact base's global positive mean floor as
the `rho` required by the asymptotic constructor. -/
theorem nonempty_quantitativeNearRoundTailDecayAnalyticData3_of_uniformRelativeDecay_of_baseMeanFloor
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundCompactFlowBaseData3.{u, v}
        M)
    {t0 : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t).leviCivita 1]
    (ht0 : 0 ≤ t0)
    (hTraceless : UniformRelativeTracelessRicciDecayAtTop3 data.gt t0)
    (hOscillation :
      UniformRelativeScalarMeanOscillationDecayAtTop3 data.gt t0) :
    Nonempty
      (NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
        M) := by
  apply
    data.nonempty_quantitativeNearRoundTailDecayAnalyticData3_of_uniformRelativeDecay
      ht0 data.meanScalarFloor_pos _ hTraceless hOscillation
  intro s hs
  exact data.meanScalarLower
    ⟨t0 + s, add_nonneg ht0 hs⟩

end NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundCompactFlowBaseData3

/-- End-to-end analytic input which postpones selection of the common
near-round tail.  It stores only compact flow data, a nonnegative reference
time, and the two uniform decay contracts. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  compact :
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundCompactFlowBaseData3.{u, v}
      M
  referenceTime : ℝ
  referenceTime_nonneg : 0 ≤ referenceTime
  relativeTracelessRicciDecay :
    UniformRelativeTracelessRicciDecayAtTop3 compact.gt referenceTime
  relativeScalarMeanOscillationDecay :
    UniformRelativeScalarMeanOscillationDecayAtTop3 compact.gt referenceTime

namespace NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Select the synchronized tail internally and obtain the quantitative
near-round package consumed by eventual Hamilton decay. -/
noncomputable def toQuantitativeNearRoundTailDecayAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundTailDecayAnalyticData3.{u, v}
      M :=
  Classical.choice
    (data.compact.nonempty_quantitativeNearRoundTailDecayAnalyticData3_of_uniformRelativeDecay_of_baseMeanFloor
      data.referenceTime_nonneg data.relativeTracelessRicciDecay
        data.relativeScalarMeanOscillationDecay)

/-- The same selected quantitative tail reaches the compact moving-measure
sphere endpoint. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toQuantitativeNearRoundTailDecayAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureQuantitativeNearRoundFromDecayAnalyticData3

end Poincare
