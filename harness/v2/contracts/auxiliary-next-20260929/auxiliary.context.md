# Source context for the corrected auxiliary estimate

Read nearest definitions and actual imports when using further symbols.

## Poincare/Global/HamiltonScalarGradientEstimate.lean:390-518

```lean
  linarith

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] in
/-- Hamilton's contracted-Bianchi improvement of the scalar trace-gradient bound. -/
theorem scalarGradNormSq_le_twentySevenths_covRicciNormSq
    (g : Poincare.ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt g x ≤
      (20 / 7 : ℝ) * Poincare.covRicciNormSqAt g x := by
  classical
  letI : FiniteDimensional ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Poincare.ClosedSmoothModel 3))
  let b := Poincare.metricOrthogonalBasisAt g x
  let d := fun i ↦ g.metricBilinAt x (b i) (b i)
  let D := fun a ↦ extDerivFun (fun y ↦ g.scalarAt y) x (b a)
  let C := fun a i j ↦
    Poincare.covTensor2DerivAt g (Poincare.ricciVariationField g) x (b a) (b i) (b j)
  have hcard : Fintype.card (Fin (Module.finrank ℝ
      (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x))) = 3 := by
    simp [Poincare.ClosedSmoothRiemannianMetric.finrank_tangentSpace_eq (n := 3) (M := M) x]
  have hd : ∀ i, 0 < d i := fun i ↦ g.metricBilinAt_pos x (b.ne_zero i)
  have ht : ∀ a, ∑ i, C a i i / d i = D a := by
    intro a
    exact (g.extDerivFun_scalarAt_eq_metricOrthogonalBasis_covRicci_trace x (b a)).symm
  have hv : ∀ j, ∑ a, C a a j / d a = D j / 2 := by
    intro j
    exact Poincare.HamiltonScalarGradientEstimate.contractedBianchi_orthogonal_trace g x (b j)
  have hs : ∀ a i j, C a i j = C a j i := fun a i j ↦
    Poincare.covTensor2DerivAt_ricciVariationField_symm g x (b a) (b i) (b j)
  rw [g.scalarGradNormSqAt_eq_metricOrthogonalBasis_sum x,
    Poincare.covRicciNormSqAt_eq_metricOrthogonalBasis_sum g x]
  exact Poincare.HamiltonScalarGradientEstimate.weighted_bianchi_gradient_bound
    hcard d D C hd ht hv hs

/-- Contracted Bianchi supplies strict derivative-energy damping along normalized flow. -/
theorem tracelessEnergy_evolution_damped
    {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hJoint : ∀ s y, Poincare.MetricEntriesJointContDiffAt gt s y 3)
    (hFlow : ∀ y, Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t y) :
    deriv (fun s ↦ (gt s).tracelessRicciNormSqAt x) t -
        (gt t).laplacianAt (fun y ↦ (gt t).tracelessRicciNormSqAt y) x ≤
      -(2 / 21 : ℝ) * Poincare.covRicciNormSqAt (gt t) x +
      (gt t).pinchingTracelessRicciReactionTrace3At x
        ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x) -
        (4 / 3 : ℝ) * Poincare.meanScalar (gt t) * (gt t).tracelessRicciNormSqAt x := by
  letI : Nonempty M := ⟨x⟩
  have hd :=
    Poincare.hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
      (x := x) hFlow hJoint
  rw [hd.deriv]
  dsimp only [Poincare.normalizedTracelessRicciEvolutionReactionAt]
  have hb := Poincare.HamiltonScalarGradientEstimate.factorTwentySevenths_damping
    (Poincare.HamiltonScalarGradientEstimate.scalarGradNormSq_le_twentySevenths_covRicciNormSq
      (gt t) x)
  linarith

end Poincare.HamiltonScalarGradientEstimate

namespace Poincare.HamiltonScalarGradientEstimate

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Positive scalar curvature and a Ricci quotient at most one bound the actual
three-dimensional cubic reaction by `4 R |Ric°|²`. -/
theorem cubic_reaction_le_four_scalar_mul_traceless
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (hR : 0 < g.scalarAt x) (hq : g.pinchingQuotientAt x ≤ 1) :
    g.pinchingTracelessRicciReactionTrace3At x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤
      4 * g.scalarAt x * g.tracelessRicciNormSqAt x := by
  have hrem := g.pinchingReactionRemainderAt_nonpos_of_scalar_pos rfl hR
  have hC : g.scalarAt x * g.pinchingRicciNormReactionMotionTraceCubicAt x ≤
      4 * g.ricciNormSqAt x ^ 2 := by
    have hfactor : g.scalarAt x / 2 *
        (g.scalarAt x * g.pinchingRicciNormReactionMotionTraceCubicAt x -
          4 * g.ricciNormSqAt x ^ 2) ≤ 0 := by
      convert hrem using 1
      simp only [ClosedSmoothRiemannianMetric.pinchingReactionRemainderAt,
        ClosedSmoothRiemannianMetric.pinchingScalarReactionAt]
      ring
    have hnonpos :=
      nonpos_of_mul_nonpos_right hfactor (div_pos hR (by norm_num : (0 : ℝ) < 2))
    linarith
  have hN : g.ricciNormSqAt x ≤ g.scalarAt x ^ 2 := by
    have hq' : g.ricciNormSqAt x / g.scalarAt x ^ 2 ≤ 1 := hq
    simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos hR)).mp hq'
  have hU := g.tracelessRicciNormSqAt_nonneg x (by norm_num)
  have hNU := mul_le_mul_of_nonneg_right hN hU
  have hT : g.scalarAt x *
      g.pinchingTracelessRicciReactionTrace3At x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤
      4 * g.ricciNormSqAt x * g.tracelessRicciNormSqAt x := by
    simp only [ClosedSmoothRiemannianMetric.pinchingTracelessRicciReactionTrace3At,
      ClosedSmoothRiemannianMetric.pinchingScalarReactionAt,
      ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt]
    nlinarith [hC]
  apply le_of_mul_le_mul_left ?_ hR
  calc
    g.scalarAt x * g.pinchingTracelessRicciReactionTrace3At x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤
        4 * g.ricciNormSqAt x * g.tracelessRicciNormSqAt x := hT
    _ ≤ 4 * g.scalarAt x ^ 2 * g.tracelessRicciNormSqAt x := by nlinarith [hNU]
    _ = g.scalarAt x * (4 * g.scalarAt x * g.tracelessRicciNormSqAt x) := by ring

end Poincare.HamiltonScalarGradientEstimate
```

## Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:1-45

```lean
import Poincare.Global.NormalizedFlowRicciTensorEvolution
import Poincare.Global.NormalizedFlowScalarLowerProfile
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay
import Poincare.Global.NormalizedFlowHausdorffSpatialMixedRegularity

/-!
# Forward traceless-Ricci decay from the actual normalized flow reaction

This file removes the raw pointwise evolution hypothesis from the normalized
traceless-Ricci reaction-decay route.  The lower Ricci evolution is supplied by
an actual normalized Ricci flow and joint `C³` metric entries; the scalar
evolution is supplied by the assembled Lichnerowicz formula.  We also compute
the inverse-metric part of the Ricci-norm reaction under normalized flow, so
the resulting reaction is a proof-free algebraic expression.
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

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3
local notation "TM" => (TangentSpace I : M → Type _)

/-!
## The normalized inverse-metric reaction
-/

/-- Under normalized Ricci flow, the inverse-metric part of the Ricci-norm
derivative is the usual cubic term minus the spatially constant scaling term.
This is the precise point at which normalized and unnormalized flow differ in
the `|Ric|^2` evolution. -/
theorem
```

## Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:185-237

```lean
            ricciEvolution3ReactionRHSAt g y u w) x := by
    simpa [g, δRic3, hRic3, L] using
      trace_metricRaise_ricciDerivativeDual_comp_ricciEndo_eq_pairing
        (gt := gt) (t₀ := t₀) (x := x) hRic3
        (fun y : M ↦ fun u w : TM y ↦
          ricciEvolution3ReactionRHSAt g y u w)
        (fun _ _ ↦ rfl)
  have hReactionPairing :=
    metricVariationRicciPairingAt_ricciEvolution3ReactionRHSAt g x
  unfold ricciEvolutionPinchingReactionMotionTraceAt
  dsimp only
  unfold ClosedSmoothRiemannianMetric.pinchingRicciNormReactionMotionTraceAt
  rw [hTraceSplit, hTraceK, hTraceL, hReactionPairing]
  unfold ClosedSmoothRiemannianMetric.pinchingRicciNormReactionMotionTraceCubicAt
  ring

/-!
## Exact normalized traceless-Ricci evolution
-/

/-- Scalar-square parabolic form for volume-normalized Ricci flow. -/
theorem
    hasDerivAt_scalarAt_sq_of_satisfiesNormalizedHamiltonScalarEvolutionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hHam : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ x)
    (hScalar₂ :
      ∀ y : M, ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y) :
    HasDerivAt (fun t ↦ (gt t).scalarAt x ^ 2)
      ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
        - 2 * (gt t₀).scalarGradNormSqAt x
        + 4 * (gt t₀).scalarAt x * (gt t₀).ricciNormSqAt x
        - (4 / 3 : ℝ) * meanScalar (gt t₀) *
            (gt t₀).scalarAt x ^ 2) t₀ := by
  have hsq_lap :=
    (gt t₀).laplacianAt_sq
      (f := fun y : M ↦ (gt t₀).scalarAt y) (x := x) hScalar₂
  have hprod :
      HasDerivAt
        (fun t ↦ (gt t).scalarAt x * (gt t).scalarAt x)
        ((((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
              + 2 * (gt t₀).ricciNormSqAt x
              - (2 / 3 : ℝ) * meanScalar (gt t₀) *
                  (gt t₀).scalarAt x) * (gt t₀).scalarAt x
          + (gt t₀).scalarAt x *
            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
              + 2 * (gt t₀).ricciNormSqAt x
              - (2 / 3 : ℝ) * meanScalar (gt t₀) *
                  (gt t₀).scalarAt x))) t₀ := by
    simpa [SatisfiesNormalizedHamiltonScalarEvolutionAt] using hHam.mul hHam
  have htarget :
```

## Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:470-525

```lean
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt) :
    HasDerivAt (fun t ↦ (gt t).tracelessRicciNormSqAt x)
      ((gt t₀).laplacianAt
          (fun y : M ↦ (gt t₀).tracelessRicciNormSqAt y) x
        + normalizedTracelessRicciEvolutionReactionAt (gt t₀) x) t₀ := by
  apply
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_scalarEvolution
      hFlow hJoint
  exact
    satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
      hFlow hLichnerowicz

/-- Global joint `C³` metric entries construct the Lichnerowicz package and
therefore make the exact normalized `|Ric°|²` evolution fully automatic from
the normalized flow equation. -/
theorem
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3) :
    HasDerivAt (fun t ↦ (gt t).tracelessRicciNormSqAt x)
      ((gt t₀).laplacianAt
          (fun y : M ↦ (gt t₀).tracelessRicciNormSqAt y) x
        + normalizedTracelessRicciEvolutionReactionAt (gt t₀) x) t₀ := by
  exact
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_globalLichnerowicz
      hFlow (hJoint t₀)
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)

/-!
## Downstream decay and finite energy with no raw evolution witness
-/

/-- Coercive domination of the explicit normalized reaction now directly
implies uniform exponential pointwise decay. -/
theorem
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_actualNormalizedReaction_domination_of_normalizedFlow_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hJointMetricEntries : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    {rate : ℝ}
    (hReaction : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
        -rate * (gt t).tracelessRicciNormSqAt x) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
```

## Poincare/Global/NormalizedFlowScalarLowerProfile.lean:1-92

```lean
import Poincare.Global.HamiltonScalarNegativeBarrier
import Poincare.Global.NormalizedFlowScalarRegularity

/-!
# Positive scalar lower profiles for normalized Ricci flow

For volume-normalized Ricci flow the scalar equation contains the spatially
constant damping term

`-(2 / 3) * meanScalar * R`.

Consequently an initially positive scalar curvature does not by itself give a
time-independent positive floor.  The natural preserved quantity uses the
normalization integrating factor.  This file proves the corresponding strict
parabolic comparison and records the precise extra condition under which it
does become a uniform positive floor: the normalization primitive must be
bounded above.
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

local notation "I" => closedSmoothModelWithCorners 3

/-- The pointwise scalar equation for three-dimensional volume-normalized
Ricci flow. -/
def SatisfiesNormalizedHamiltonScalarEvolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) (x : M)
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1] :
    Prop :=
  HasDerivAt (fun s ↦ (gt s).scalarAt x)
    ((gt t).laplacianAt (fun y ↦ (gt t).scalarAt y) x +
      2 * (gt t).ricciNormSqAt x -
      (2 / 3 : ℝ) * meanScalar (gt t) * (gt t).scalarAt x) t

/-- The normalized metric equation plus the assembled Lichnerowicz scalar
variation proves the actual normalized scalar equation. -/
theorem satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t y)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt) :
    SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x := by
  have hScalarTwo : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t).scalarAt z) y :=
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      hFlow (hLichnerowicz.timeVariationEntries t)
  have hDerivative := hLichnerowicz.hasDerivAt_scalar_stokes t x
  rw [scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt_of_normalizedFlow
      hFlow (by norm_num) hScalarTwo,
    metricVariationRicciPairingAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      (hFlow x)] at hDerivative
  unfold SatisfiesNormalizedHamiltonScalarEvolutionAt
  convert hDerivative using 1
  ring

/-- Strict positivity of scalar curvature on one compact slice has a uniform
positive numerical floor. -/
theorem exists_pos_scalar_floor_of_forall_scalarAt_pos
    [Nonempty M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hScalarPos : ∀ x : M, 0 < g.scalarAt x) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ x : M, rho ≤ g.scalarAt x := by
  obtain ⟨xmin, _hxmin, hmin⟩ :=
    isCompact_univ.exists_isMinOn
      (Set.univ_nonempty)
      (fun y _ ↦ (scalarAt_continuous g).continuousAt.continuousWithinAt)
  exact ⟨g.scalarAt xmin, hScalarPos xmin, fun x ↦ hmin trivial⟩

/-- Strict comparison with any positive solution of the scalar normalization
ODE `phi' = -(2/3) meanScalar * phi` on one compact forward interval.

The positive `2 |Ric|²` reaction leaves a strictly positive `phi²` remainder
after factorization, so the strict minimum principle applies without an a
priori upper bound for scalar curvature or mean scalar curvature. -/
theorem normalizedFlow_scalarAt_gt_of_normalization_profile
```

## Poincare/Global/IntrinsicBochnerScalarGradient.lean:340-398

```lean
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f) := by
  filter_upwards [transported_gradient_eventuallyEq g x f hf,
    GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x,
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hgrad hone hz
  have hG := CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric g.inner x hone
  rw [RicciFlow.RicciFlow.coordGradNormSq, anchorBlendedMetricFlow, hG, ← hgrad]
  rw [CovariantDerivative.chartMetric_apply,
    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
  rw [(isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse]
  rfl

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A C³ scalar has a C² squared gradient norm. -/
theorem gradientNormSq_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric 3 M) (f : M → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 f) (x : M) :
    ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) x := by
  let G := anchorBlendedMetricFlow (fun _ ↦ g) x 0
  let q := extChartAt (closedSmoothModelWithCorners 3) x x
  let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f
  have hu : ContDiffAt ℝ 3 u q := by
    have hi := (contMDiffOn_extChartAt_symm (n := 3) x q (mem_extChartAt_target x)).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    apply (hf.contMDiffAt.comp q hi).contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with z hz
    exact indicator_of_mem hz _
  have hGtop : ContDiff ℝ ∞ G := CovariantDerivative.contDiff_blendedChartMetric
    (GeodesicTransport.cutoff (n := 3) x) GeodesicTransport.backgroundMetric
    g.inner x (by simp) (GeodesicTransport.cutoff_contDiff x)
    (GeodesicTransport.cutoff_tsupport x) g.contMDiff_inner
  have hG : ContDiffAt ℝ 2 G q := (hGtop.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hInv : ContDiffAt ℝ 2 (fun z ↦ (G z).inverse) q :=
    (anchorBlendedMetricFlow_isInvertible (fun _ ↦ g) x 0 q).contDiffAt_map_inverse.comp q hG
  have hd : ContDiffAt ℝ 2 (RicciFlow.RicciFlow.coordGradient G u) q :=
    hInv.clm_apply (hu.fderiv_right (by norm_num))
  have hnorm : ContDiffAt ℝ 2 (RicciFlow.RicciFlow.coordGradNormSq G u) q :=
    (hG.clm_apply hd).clm_apply hd
  have hcomp := hnorm.contMDiffAt.comp x
    (contMDiffAt_extChartAt : ContMDiffAt (closedSmoothModelWithCorners 3)
      𝓘(ℝ, ClosedSmoothModel 3) 2 (extChartAt (closedSmoothModelWithCorners 3) x) x)
  apply hcomp.congr_of_eventuallyEq
  have heq := (continuousAt_extChartAt (I := closedSmoothModelWithCorners 3) x).eventually
    (gradientNormSq_eventuallyEq_coordGradNormSq g x f (hf.mdifferentiable (by norm_num)))
  filter_upwards [heq, (isOpen_extChartAt_source (I := closedSmoothModelWithCorners 3) x).mem_nhds
    (mem_extChartAt_source x)] with y hy hys
  rw [(extChartAt (closedSmoothModelWithCorners 3) x).left_inv hys] at hy
  exact hy

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Differentiation does not enlarge the topological support of a scalar's
squared gradient norm. -/
theorem gradientNormSq_tsupport_subset
    (g : ClosedSmoothRiemannianMetric 3 M) (f : M → ℝ) :
    tsupport (fun y ↦ g.inner y (g.gradientAt f y) (g.gradientAt f y)) ⊆ tsupport f := by
  intro x hx
  by_contra hxf
  have heq := (notMem_tsupport_iff_eventuallyEq.mp hxf).eventually_nhds
```

## Poincare/Global/IntrinsicBochnerScalarGradient.lean:843-942

```lean
/-- Fourth-order joint metric entries give joint C² scalar curvature. -/
theorem scalar_jointContDiffAt_two_of_metricEntries_four
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hJoint4 : ∀ t y, MetricEntriesJointContDiffAt gt t y 4) (t : ℝ) (x : M) :
    ContDiffAt ℝ 2
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) :=
  scalar_jointContDiffAt 2 (hJoint4 t x)

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Fifth-order joint metric entries give the spatial C³ scalar required by Bochner. -/
theorem scalar_contMDiff_three_of_metricEntries_five
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hJoint5 : ∀ t y, MetricEntriesJointContDiffAt gt t y 5) (t : ℝ) :
    ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 (fun y ↦ (gt t).scalarAt y) :=
  fun x ↦ scalar_contMDiffAt_of_metricEntries 3 (hJoint5 t x)

/-- Fifth-order joint entries supply both extra scalar hypotheses of the time theorem. -/
theorem scalarRegularity_of_metricEntries_five
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hJoint5 : ∀ t y, MetricEntriesJointContDiffAt gt t y 5) (t : ℝ) (x : M) :
    ContDiffAt ℝ 2
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x) ∧
    MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ)
      (fun y ↦ (gt t).laplacianAt (fun z ↦ (gt t).scalarAt z) y) x := by
  exact ⟨scalar_jointContDiffAt_two_of_metricEntries_four
      (fun s y ↦ (hJoint5 s y).of_le (by norm_num)) t x,
    laplacianAt_mdifferentiableAt_of_contMDiff_three (gt t) _
      (scalar_contMDiff_three_of_metricEntries_five hJoint5 t) x⟩

/-- The scalar-gradient evolution equation after the Ricci terms cancel. -/
def SatisfiesScalarGradientEvolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) (x : M) : Prop :=
    let g := gt t
    let R : M → ℝ := fun y ↦ g.scalarAt y
    HasDerivAt (fun s ↦ (gt s).scalarGradNormSqAt x)
      (g.laplacianAt (fun y ↦ g.scalarGradNormSqAt y) x -
        ((2 : ℕ) : ℝ) * (∑ i, g.inner x
          (g.leviCivita (g.gradient R) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
          (g.leviCivita (g.gradient R) x
            (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))) +
        ((4 : ℕ) : ℝ) * g.inner x (g.gradientAt R x) (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) -
        ((2 : ℕ) : ℝ) * meanScalar g * g.scalarGradNormSqAt x) t

variable [SecondCountableTopology M]

/-- Assemble the evolution equation from intrinsic Bochner and the time
variation theorem. The remaining scalar regularity requirements are explicit. -/
theorem satisfiesScalarGradientEvolutionAt_of_normalizedFlow_of_scalarRegularity
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (hJoint : ∀ s y, MetricEntriesJointContDiffAt gt s y 3)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y)
    (hScalarJoint : ContDiffAt ℝ 2
      (fun p : ℝ × ClosedSmoothModel 3 ↦
        (gt p.1).scalarAt ((extChartAt (closedSmoothModelWithCorners 3) x).symm p.2))
      (t, extChartAt (closedSmoothModelWithCorners 3) x x))
    (hScalarThree : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3
      (fun y ↦ (gt t).scalarAt y)) :
    SatisfiesScalarGradientEvolutionAt gt t x := by
  have hd := ScalarGradientEvolution.hasDerivAt_scalarGradNormSq_normalizedFlow
    hJoint hFlow hScalarJoint
    (laplacianAt_mdifferentiableAt_of_contMDiff_three (gt t) _ hScalarThree x)
  have hb := bochner (gt t) (fun y ↦ (gt t).scalarAt y) hScalarThree x
  change (gt t).laplacianAt (fun y ↦ (gt t).scalarGradNormSqAt y) x = _ at hb
  apply hd.congr_deriv
  dsimp only [SatisfiesScalarGradientEvolutionAt]
  rw [hb]
  ring

/-- Normalized flow and fifth-order joint metric entries give the intrinsic
scalar-gradient evolution equation, with no extra scalar hypotheses. -/
theorem satisfiesScalarGradientEvolutionAt_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
    (hJoint5 : ∀ s y, MetricEntriesJointContDiffAt gt s y 5)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y) :
    SatisfiesScalarGradientEvolutionAt gt t x :=
  satisfiesScalarGradientEvolutionAt_of_normalizedFlow_of_scalarRegularity
    (fun s y ↦ (hJoint5 s y).of_le (by norm_num)) hFlow
    (scalarRegularity_of_metricEntries_five hJoint5 t x).1
    (scalar_contMDiff_three_of_metricEntries_five hJoint5 t)

end Poincare.IntrinsicBochnerScalarGradient
```

## Poincare/Global/MetricFlowJointPinchingEvolution.lean:80-185

```lean
        (fun y : M ↦
          g.ricciAt y (gramFrame x y c) (gramFrame x y d)) x := by
      simpa [ricciVariationField, gramFrame, b] using hRic (b c) (b d)
    exact (((hac.smul hbd).smul hab).smul hcd)
  exact hsum.congr_of_eventuallyEq
    ((gramMatrix_eventually_isUnit (g := g) x).mono fun y hy ↦ by
      calc
        g.ricciNormSqAt y =
            metricVariationRicciPairingAt g (ricciVariationField g) y :=
          (metricVariationRicciPairingAt_ricci g y).symm
        _ = rhs y := by
          simpa [rhs] using
            metricVariationRicciPairingAt_ricci_eq_sum_gram_inv g x y hy)

/-- The squared Ricci norm of a closed smooth metric is canonically `C²`. -/
theorem ricciNormSqAt_contMDiffAt_two_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x := by
  exact contMDiffAt_two_ricciNormSqAt_of_ricci_entries g x
    (covTensor2ExtContMDiffAt_ricciVariationField_canonical g x)

/-- The Bochner pairing field is differentiable once `|Ric|²` is `C²`. -/
theorem covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hNorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x)
    (w : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ covRicciRicciPairingAt g y (extend E w y)) x := by
  let f : M → ℝ := fun y ↦ g.ricciNormSqAt y
  let W : ∀ y : M, TM y := extend E w
  have hW : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% W) x := by
    simpa [W] using (mdifferentiableAt_extend I E w)
  have hd : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ extDerivFun f y (W y)) x := by
    exact CovariantDerivative.mdiffAt_extDerivFun_apply hNorm hW
  have heq :
      (fun y : M ↦ covRicciRicciPairingAt g y (W y)) =
        fun y : M ↦ (1 / 2 : ℝ) * extDerivFun f y (W y) := by
    funext y
    have h := extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
      g y (W y)
    change extDerivFun f y (W y) = 2 * covRicciRicciPairingAt g y (W y) at h
    rw [h]
    ring
  rw [heq]
  exact mdifferentiableAt_const.mul hd

/-- A nonzero scalar denominator makes the ordinary pinching quotient `C²`. -/
theorem contMDiffAt_two_pinchingQuotientAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hNorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x)
    (hScalar : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x)
    (hR : g.scalarAt x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.pinchingQuotientAt y) x := by
  have hden : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (g.scalarAt y) ^ 2) x := by
    simpa [pow_two] using hScalar.smul hScalar
  have hinv : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ ((g.scalarAt y) ^ 2)⁻¹) x :=
    hden.inv₀ (pow_ne_zero 2 hR)
  simpa [ClosedSmoothRiemannianMetric.pinchingQuotientAt,
    div_eq_mul_inv] using hNorm.smul hinv

/-- The trace-form traceless Ricci norm inherits `C²` regularity. -/
theorem contMDiffAt_two_tracelessRicciNormSqAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hNorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x)
    (hScalar : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.tracelessRicciNormSqAt y) x := by
  have hc : ContMDiffAt I 𝓘(ℝ) 2
      (fun _ : M ↦ ((n : ℝ)⁻¹)) x := contMDiffAt_const
  have hsquare : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (g.scalarAt y) ^ 2) x := by
    simpa [pow_two] using hScalar.smul hScalar
  simpa [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt,
    div_eq_mul_inv, mul_comm] using hNorm.sub (hc.smul hsquare)

/-- Composition with a nonzero-base real power preserves manifold `C²`. -/
theorem contMDiffAt_two_rpow_const_of_ne
    {f : M → ℝ} {x : M} (p : ℝ)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hfx : f x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ f y ^ p) x := by
  have hp : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) 2 (fun r : ℝ ↦ r ^ p) (f x) :=
    contMDiffAt_iff_contDiffAt.mpr
      (Real.contDiffAt_rpow_const_of_ne hfx)
  exact hp.comp x hf

/-- A positive scalar denominator makes the improved traceless quotient `C²`. -/
theorem contMDiffAt_two_tracelessPinchingAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (delta : ℝ)
    (hTraceNorm : ContMDiffAt I 𝓘(ℝ) 2
```

## Poincare/Global/Laplacian.lean:730-817

```lean
The gradient-field differentiability hypotheses are carried for ledger task
`M1-lc-regularity`.
-/
theorem laplacianAt_add (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.laplacianAt (f + h) x = g.laplacianAt f x + g.laplacianAt h x := by
  unfold laplacianAt
  rw [g.hessianDualAt_add hf hh hgradf hgradh]
  simp [LinearMap.comp_add]

/--
Additivity of the scalar Laplacian with the gradient-field regularity
discharged from pointwise `C²` scalar regularity.
-/
theorem laplacianAt_add' (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y)
    (hh : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 h y) :
    g.laplacianAt (f + h) x = g.laplacianAt f x + g.laplacianAt h x :=
  g.laplacianAt_add
    (fun y ↦ (hf y).mdifferentiableAt two_ne_zero)
    (fun y ↦ (hh y).mdifferentiableAt two_ne_zero)
    (g.mdifferentiableAt_gradient (hf x))
    (g.mdifferentiableAt_gradient (hh x))

/--
Homogeneity of the scalar Laplacian.

The gradient-field differentiability hypothesis is carried for ledger task
`M1-lc-regularity`.
-/
theorem laplacianAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M} (c : ℝ)
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    g.laplacianAt (c • f) x = c * g.laplacianAt f x := by
  unfold laplacianAt
  rw [g.hessianDualAt_const_smul c hf hgradf]
  simp [LinearMap.comp_smul, smul_eq_mul]

/--
Homogeneity of the scalar Laplacian with the gradient-field regularity
discharged from pointwise `C²` scalar regularity.
-/
theorem laplacianAt_const_smul' (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M} (c : ℝ)
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y) :
    g.laplacianAt (c • f) x = c * g.laplacianAt f x :=
  g.laplacianAt_const_smul c
    (fun y ↦ (hf y).mdifferentiableAt two_ne_zero)
    (g.mdifferentiableAt_gradient (hf x))

theorem laplacianAt_mul (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.laplacianAt (f * h) x =
      f x * g.laplacianAt h x + h x * g.laplacianAt f x
        + 2 * g.inner x (g.gradientAt f x) (g.gradientAt h x) := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  let A := (LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm.toLinearMap
  have hcross : ∀ φ ψ : TM x →L[ℝ] ℝ,
      LinearMap.trace ℝ (TM x)
        (A ∘ₗ
          (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
            ((φ.smulRight ψ).toLinearMap))) =
      φ ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm
          (LinearMap.toContinuousLinearMap.symm ψ)) := by
    intro φ ψ
    have hcomp : A ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          ((φ.smulRight ψ).toLinearMap)) =
        LinearMap.smulRight (φ.toLinearMap)
          ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
            (g.metricBilinAt_nondegenerate x)).symm
            (LinearMap.toContinuousLinearMap.symm ψ)) := by
      apply LinearMap.ext
      intro v
      have h1 : (φ.smulRight ψ).toLinearMap v = φ v • ψ := rfl
```

## Poincare/Global/Laplacian.lean:860-885

```lean
    (fun y ↦ (hh y).mdifferentiableAt two_ne_zero)
    (g.mdifferentiableAt_gradient (hf x))
    (g.mdifferentiableAt_gradient (hh x))

theorem laplacianAt_sq (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y) :
    g.laplacianAt (fun y ↦ f y ^ 2) x =
      2 * f x * g.laplacianAt f x +
        2 * g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
  have hfun : (fun y : M ↦ f y ^ 2) = f * f := by
    funext y
    simp [Pi.mul_apply, pow_two]
  rw [hfun, g.laplacianAt_mul' hf hf]
  ring

theorem laplacianAt_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (x : M) :
    g.laplacianAt (fun _ : M ↦ c) x = 0 := by
  unfold laplacianAt
  rw [g.hessianDualAt_const c x]
  simp

end ClosedSmoothRiemannianMetric
end Poincare
```

## Poincare/Global/RicciNorm.lean:100-122

```lean

/-- The tangent fiber has the same real dimension as the closed smooth model. -/
theorem finrank_tangentSpace_eq (x : M) :
    Module.finrank ℝ (TM x) = n := by
  rw [show Module.finrank ℝ (TM x) = Module.finrank ℝ E from rfl,
    finrank_euclideanSpace_fin]

/-- The pointwise Ricci pinching inequality `R^2 <= n |Ric|^2`. -/
theorem scalarAt_sq_le_nat_mul_ricciNormSqAt (x : M) :
    g.scalarAt x ^ 2 ≤ n * g.ricciNormSqAt x := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hsa : ∀ p q : TM x,
      g.metricBilinAt x (g.ricciEndoAt x p) q =
        g.metricBilinAt x p (g.ricciEndoAt x q) := by
    intro p q
    simpa [metricBilinAt] using g.ricciEndoAt_selfAdjoint x p q
  have h := RicciFlow.trace_sq_le_card_mul_trace_comp_self
    (b := g.metricBilinAt x)
    (hbs := g.metricBilinAt_isSymm x)
    (hbpos := fun v hv => g.metricBilinAt_pos x hv)
    (A := g.ricciEndoAt x) hsa
```

## Poincare/Global/RicciNorm.lean:184-200

```lean

/-- The Cauchy-Schwarz pinching gap `n |Ric|^2 - R^2`. -/
noncomputable def pinchingGapAt (x : M) : ℝ :=
  n * g.ricciNormSqAt x - (g.scalarAt x) ^ 2

/-- The squared traceless-Ricci norm in scalar trace form: `|Ric|^2 - R^2/n`. -/
noncomputable def tracelessRicciNormSqAt (x : M) : ℝ :=
  g.ricciNormSqAt x - (g.scalarAt x) ^ 2 / n

/-- The definition of the trace-form squared traceless-Ricci norm. -/
theorem tracelessRicciNormSqAt_eq (x : M) :
    g.tracelessRicciNormSqAt x =
      g.ricciNormSqAt x - (g.scalarAt x) ^ 2 / n :=
  rfl

/-- The pinching gap is `n` times the trace-form traceless-Ricci norm. -/
theorem pinchingGapAt_eq_nat_mul_tracelessRicciNormSqAt
```
