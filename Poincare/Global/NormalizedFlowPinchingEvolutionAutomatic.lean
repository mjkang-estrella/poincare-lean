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

set_option maxHeartbeats 12000000 in
/-- The improved quotient has an additional nonpositive normalization term. -/
theorem satisfiesTracelessPinchingImprovementEvolutionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ δ : ℝ}
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hFlow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hRpos : ∀ x, 0 < (gt t₀).scalarAt x)
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (x : M) :
    ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
      gt t₀ x δ ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x) := by
  letI : Nonempty M := ⟨x⟩
  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
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
  have hTraceNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.tracelessRicciNormSqAt z) y := fun y ↦
    contMDiffAt_two_tracelessRicciNormSqAt
      g y (hNorm2 y) (hScalar2 y)
  have hTraceQuot2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.tracelessPinchingAt z δ) y := fun y ↦
    contMDiffAt_two_tracelessPinchingAt
      g y δ (hTraceNorm2 y) (hScalar2 y) (hRpos y)
  have hScalarPow2SubDelta2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun z : M ↦ g.scalarAt z ^ (2 - δ)) y := fun y ↦
    contMDiffAt_two_rpow_const_of_ne
      (2 - δ) (hScalar2 y) (hRpos y).ne'
  have hTraceQuotGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.tracelessPinchingAt y δ))) x :=
    g.mdifferentiableAt_gradient (hTraceQuot2 x)
  have hScalarGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.scalarAt y))) x :=
    g.mdifferentiableAt_gradient (hScalar2 x)
  have hTraceProduct2 : ContMDiffAt I 𝓘(ℝ) 2
      ((fun y : M ↦ g.tracelessPinchingAt y δ) *
        (fun y : M ↦ g.scalarAt y ^ (2 - δ))) x := by
    simpa only [Pi.mul_apply] using
      (hTraceQuot2 x).smul (hScalarPow2SubDelta2 x)
  have hTraceProductGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient
          ((fun y : M ↦ g.tracelessPinchingAt y δ) *
            (fun y : M ↦ g.scalarAt y ^ (2 - δ))))) x :=
    g.mdifferentiableAt_gradient hTraceProduct2
  have hTraceNormGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.tracelessRicciNormSqAt y))) x :=
    g.mdifferentiableAt_gradient (hTraceNorm2 x)
  let R : ℝ := g.scalarAt x
  let N : ℝ := g.ricciNormSqAt x
  let U : ℝ := g.tracelessRicciNormSqAt x
  let Q : ℝ := g.tracelessPinchingAt x δ
  let p : ℝ := 2 - δ
  let lapU : ℝ := g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
  let A : ℝ := covRicciNormSqAt g x
  let B : ℝ := g.pinchingMixedGradientPairingAt x
  let S : ℝ := g.scalarGradNormSqAt x
  let ricciReaction : ℝ := g.pinchingRicciNormReactionMotionTraceCubicAt x
  let T : ℝ := g.pinchingTracelessRicciReactionTrace3At x ricciReaction
  let Sreact : ℝ := g.pinchingScalarReactionAt x
  let Urhs : ℝ := lapU - 2 * A + (2 / 3 : ℝ) * S + T - (4 / 3 : ℝ) * meanScalar g * U
  let Rrhs : ℝ := lapR + Sreact - (2 / 3 : ℝ) * meanScalar g * R
  have hUderiv :
      HasDerivAt (fun t ↦ (gt t).tracelessRicciNormSqAt x) Urhs t₀ := by
    convert hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
      (x := x) hFlow hJoint using 1
    dsimp [Urhs, lapU, A, S, T, ricciReaction, U, g,
      normalizedTracelessRicciEvolutionReactionAt]
    ring
  have hRderiv :
      HasDerivAt (fun t ↦ (gt t).scalarAt x) Rrhs t₀ := by
    exact satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
  have hF :
      HasDerivAt (fun t ↦ (gt t).tracelessPinchingAt x δ)
        (quotientRpowDerivativeAt R U Urhs Rrhs p) t₀ := by
    simpa [g, R, U, p] using
      ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm
        (gt := gt) (t₀ := t₀) (x := x) (δ := δ)
        hUderiv hRderiv (hRpos x)
  refine ⟨hδpos, hδle, hRpos x, ?_⟩
  refine ⟨quotientRpowDerivativeAt R U Urhs Rrhs p, hF, ?_⟩
  have hRicNormDiffX : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ g.ricciNormSqAt y) x :=
    (hNorm2 x).mdifferentiableAt two_ne_zero
  have hSpatialRaw :=
    g.tracelessPinching_spatial_expansion
      x δ (hRpos x) (hScalar2 x).continuousAt
      (fun y ↦ (hScalar2 y).mdifferentiableAt two_ne_zero)
      (fun y ↦ (hRpos y).ne')
      (fun y ↦ (hTraceQuot2 y).mdifferentiableAt two_ne_zero)
      hTraceQuotGrad hScalarGrad hTraceProductGrad hTraceNormGrad
  have hSpatial :
      g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
          + g.tracelessPinchingGradientDrift3At x δ =
        lapU / R ^ p
          - p * Q * lapR / R
          - p * (2 * B - (2 / 3 : ℝ) * R * S) / (R * R ^ p)
          + p * Q * S / R ^ 2 := by
    have hBridge :=
      g.tracelessPinching_spatial_expansion_with_numerator_bridge
        x δ hRicNormDiffX ((hScalar2 x).mdifferentiableAt two_ne_zero) hSpatialRaw
    simpa [g, R, Q, p, lapU, lapR, B, S] using hBridge
  have hReaction :
      T / R ^ p - p * U * Sreact / (R * R ^ p) =
        g.tracelessPinchingReactionTermAt x δ T := by
    simpa [g, R, U, p, T, Sreact, mul_comm, mul_left_comm, mul_assoc] using
      g.tracelessPinchingReactionTermAt_eq_rpow_reaction_expansion
        x δ T (hRpos x)
  have hQeq : Q = U / R ^ p := by
    simp [Q, U, R, p, ClosedSmoothRiemannianMetric.tracelessPinchingAt]
  have hUeq : U = N - R ^ 2 / 3 := by
    simp [U, N, R, ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt]
  have hRne : R ≠ 0 := ne_of_gt (by simpa [g, R] using hRpos x)
  have hRpm1_ne : R ^ (p - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by simpa [g, R] using hRpos x) (p - 1))
  have hRp : R ^ p = R ^ (p - 1) * R := by
    have h := Real.rpow_add_one hRne (p - 1)
    convert h using 2
    ring_nf
  have hRp2 : R ^ (p + 2) = R ^ p * R ^ 2 := by
    have h1 := Real.rpow_add_one hRne p
    have h2 := Real.rpow_add_one hRne (p + 1)
    rw [show p + 2 = p + 1 + 1 by ring, h2, h1]
    ring
  have hAlg :
      quotientRpowDerivativeAt R U Urhs Rrhs p =
        (lapU / R ^ p
          - p * Q * lapR / R
          - p * (2 * B - (2 / 3 : ℝ) * R * S) / (R * R ^ p)
          + p * Q * S / R ^ 2)
          + (T / R ^ p - p * U * Sreact / (R * R ^ p))
          + PinchingAlgebra.tracelessPinchingGradientNumerator3 R N A B S δ /
            R ^ (p + 2) - (2 / 3 : ℝ) * δ * meanScalar g * Q := by
    dsimp [Urhs, Rrhs]
    unfold quotientRpowDerivativeAt PinchingAlgebra.tracelessPinchingGradientNumerator3
    rw [hQeq, hUeq, hRp2, hRp]
    field_simp [hRne, hRpm1_ne]
    dsimp [p]
    ring
  have hGrad :
      PinchingAlgebra.tracelessPinchingGradientNumerator3 R N A B S δ ≤ 0 := by
    have hδ0 : 0 ≤ δ := le_of_lt hδpos
    have hδ2 : δ ≤ 2 := by linarith
    simpa [g, R, N, A, B, S] using
      g.tracelessPinchingGradientNumerator3At_nonpos rfl hδ0 hδ2 x
  have hGradDiv :
      PinchingAlgebra.tracelessPinchingGradientNumerator3 R N A B S δ /
          R ^ (p + 2) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg hGrad
      (le_of_lt (Real.rpow_pos_of_pos (by simpa [g, R] using hRpos x) (p + 2)))
  have hMean : 0 ≤ meanScalar g := by
    obtain ⟨rho, hrho, hlow⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos g hRpos
    exact (meanScalar_pos_of_forall_scalarAt_ge g hrho hlow).le
  have hQnonneg : 0 ≤ Q := by
    rw [hQeq]
    exact div_nonneg (g.tracelessRicciNormSqAt_nonneg x (by norm_num))
      (Real.rpow_pos_of_pos (hRpos x) p).le
  have hNormalization : 0 ≤ (2 / 3 : ℝ) * δ * meanScalar g * Q :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδpos.le) hMean) hQnonneg
  rw [hAlg, ← hSpatial, hReaction]
  change _ ≤ g.laplacianAt (fun y ↦ g.tracelessPinchingAt y δ) x +
    g.tracelessPinchingGradientDrift3At x δ + g.tracelessPinchingReactionTermAt x δ T
  linarith

end Poincare.NormalizedFlowPinchingEvolutionAutomatic
