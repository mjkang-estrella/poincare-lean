import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowJointPinchingRegularity

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false

universe u

namespace Poincare.NormalizedFlowPinchingEvolutionAutomatic

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3
local notation "TM" => (TangentSpace I : M → Type _)

set_option maxHeartbeats 8000000 in
/-- The normalization terms cancel in the ordinary pinching quotient. -/
theorem satisfiesPinchingQuotientEvolutionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hFlow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hRpos : ∀ x, 0 < (gt t₀).scalarAt x) (x : M) :
    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
      gt t₀ x ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x) := by
  letI : Nonempty M := ⟨x⟩
  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
  let htime : TimeDifferentiableAt gt t₀ x :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint t₀ x).of_le (by norm_num))
  let raise' := metricRaiseDerivAt gt t₀ x htime
  let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
    satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three
      hFlow (hJoint t₀)
  have hRaise :
      HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ :=
    hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint t₀ y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow hFlow hEntries y
  have hNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.ricciNormSqAt z) y := fun y ↦
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g y (hRicC2 y)
  have hScalar2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.scalarAt z) y := fun y ↦
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries y
  have hQuot2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.pinchingQuotientAt z) y := fun y ↦
    contMDiffAt_two_pinchingQuotientAt
      g y (hNorm2 y) (hScalar2 y) (hRpos y).ne'
  have hPairDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ covRicciRicciPairingAt g y (extend E w y)) x :=
    fun w ↦
      covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
        g x (hNorm2 x) w
  have hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        g (ricciVariationField g) x :=
    covTensor2DerivExtDifferentiableAt_of_extSecond
      (g := g) (h := ricciVariationField g) (x := x)
      (covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two (hRicC2 x))
      (fun y ↦ covTensor2ExtDifferentiableAt_of_contMDiffAt_two (hRicC2 y))
      (tensor2AddLeft_ricciVariationField g)
      (tensor2SMulLeft_ricciVariationField g)
      (tensor2AddRight_ricciVariationField g)
      (tensor2SMulRight_ricciVariationField g)
  have hScalar : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ x :=
    satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
  have hScalarGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.scalarAt y))) x :=
    g.mdifferentiableAt_gradient (hScalar2 x)
  have hQuotGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.pinchingQuotientAt y))) x :=
    g.mdifferentiableAt_gradient (hQuot2 x)
  have hScalarSq2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y * g.scalarAt y) x :=
    (hScalar2 x).smul (hScalar2 x)
  have hScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient
          (fun y : M ↦ g.scalarAt y * g.scalarAt y))) x :=
    g.mdifferentiableAt_gradient hScalarSq2
  have hQuotScalarSq2 : ContMDiffAt I 𝓘(ℝ) 2
      ((fun y : M ↦ g.pinchingQuotientAt y) *
        (fun y : M ↦ g.scalarAt y * g.scalarAt y)) x := by
    simpa only [Pi.mul_apply] using (hQuot2 x).smul hScalarSq2
  have hQuotScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient
          ((fun y : M ↦ g.pinchingQuotientAt y) *
            (fun y : M ↦ g.scalarAt y * g.scalarAt y)))) x :=
    g.mdifferentiableAt_gradient hQuotScalarSq2
  have hSpatial := g.pinchingQuotient_spatial_expansion
    x (hRpos x) (hScalar2 x).continuousAt
    (fun y ↦ (hScalar2 y).mdifferentiableAt two_ne_zero)
    (fun y ↦ (hQuot2 y).mdifferentiableAt two_ne_zero)
    hScalarGrad hQuotGrad hScalarSqGrad hQuotScalarSqGrad
    (g.mdifferentiableAt_gradient (hNorm2 x))
  have hSquare := pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions
    g x (fun _ ↦ hSpatial) (hRpos x).ne'
  let R := g.scalarAt x
  let N := g.ricciNormSqAt x
  let r := meanScalar g
  let lapN := g.laplacianAt (fun y ↦ g.ricciNormSqAt y) x
  let lapR := g.laplacianAt (fun y ↦ g.scalarAt y) x
  let A := covRicciNormSqAt g x
  let C := g.pinchingRicciNormReactionMotionTraceCubicAt x
  let Nrhs := lapN - 2 * A + C - (4 / 3 : ℝ) * r * N
  let Rrhs := lapR + 2 * N - (2 / 3 : ℝ) * r * R
  have hNraw : HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x)
      (lapN - 2 * A + ricciEvolutionPinchingReactionMotionTraceAt raise' hRicci rfl) t₀ := by
    simpa [g, lapN, A, ricciEvolutionPinchingReactionMotionTraceAt] using
      hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
        hRaise hRicci rfl (hNorm2 x) hPairDiff hRicSecond
  rw [ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization
    htime (hFlow x) hRicci] at hNraw
  have hN : HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x) Nrhs t₀ := by
    convert hNraw using 1
    dsimp [Nrhs, C, r, N, g]
    ring
  have hR : HasDerivAt (fun t ↦ (gt t).scalarAt x) Rrhs t₀ := hScalar
  have hQ := ClosedSmoothRiemannianMetric.hasDerivAt_pinchingQuotientAt_of_scalar_and_ricciNorm
    hN hR (hRpos x).ne'
  refine ⟨hRpos x, _, hQ, ?_⟩
  have hAlg : ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
      (gt := gt) (t₀ := t₀) (x := x) Nrhs Rrhs =
      (lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2) +
        (2 / R ^ 4) * g.pinchingReactionRemainderAt x C := by
    change (Nrhs * R ^ 2 - N * (2 * R ^ (2 - 1) * Rrhs)) / (R ^ 2) ^ 2 = _
    dsimp [Nrhs, Rrhs]
    unfold ClosedSmoothRiemannianMetric.pinchingReactionRemainderAt
      ClosedSmoothRiemannianMetric.pinchingScalarReactionAt
    change _ = (lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2) +
      (2 / R ^ 4) * (1 / 2 * R ^ 2 * C - R * N * (2 * N))
    have hRne : R ≠ 0 := (hRpos x).ne'
    field_simp [hRne]
    ring
  rw [hAlg]
  exact le_of_eq (congrArg (fun z ↦ z + (2 / R ^ 4) * g.pinchingReactionRemainderAt x C)
    hSquare)

end Poincare.NormalizedFlowPinchingEvolutionAutomatic
