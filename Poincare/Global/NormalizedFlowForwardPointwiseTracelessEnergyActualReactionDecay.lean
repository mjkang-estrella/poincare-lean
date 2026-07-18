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
    trace_metricRaiseDeriv_ricciDual_comp_ricciEndo_eq_two_cubic_sub_normalization
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hFlow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) :
    let K : TM x →L[ℝ] TM x :=
      ((metricRaiseDerivAt gt t₀ x hgt).comp
        ((gt t₀).ricciDualContinuousAt x)).comp
        ((gt t₀).ricciEndoContinuousAt x)
    LinearMap.trace ℝ (TM x) K.toLinearMap =
      2 * (gt t₀).ricciCubicTraceAt x -
        (2 / 3 : ℝ) * meanScalar (gt t₀) * (gt t₀).ricciNormSqAt x := by
  dsimp only
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
  let b := Module.finBasis ℝ (TM x)
  let A : TM x →ₗ[ℝ] TM x := g.ricciEndoAt x
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hRaiseRic : ∀ v : TM x,
      g.metricRaiseContinuousAt x (g.ricciDualContinuousAt x v) = A v := by
    intro v
    have h := congrArg (fun L : TM x →L[ℝ] TM x ↦ L v)
      (g.ricciEndoContinuousAt_eq_metricRaise_comp_ricciDualContinuousAt x)
    simpa [A, ContinuousLinearMap.comp_apply] using h.symm
  rw [g.ricciCubicTraceAt_eq_trace x, g.ricciNormSqAt_eq_trace x,
    LinearMap.trace_eq_matrix_trace ℝ b,
    LinearMap.trace_eq_matrix_trace ℝ b,
    LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.diag_apply,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply]
  change b.coord i
      (metricRaiseDerivAt gt t₀ x hgt
        (g.ricciDualContinuousAt x
          (g.ricciEndoContinuousAt x (b i)))) =
    2 * b.coord i (((A ∘ₗ A) ∘ₗ A) (b i)) -
      (2 / 3 : ℝ) * meanScalar g *
        b.coord i ((A ∘ₗ A) (b i))
  rw [coord_eq_inner_metricDualVectorAt_of_basis
    (g := g) (x := x) (b := b)]
  rw [metricRaiseDerivAt_inner_apply hgt]
  rw [hRaiseRic]
  have hEq :=
    isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
      (gt := gt) (t₀ := t₀) (x := x) hFlow
      (A (A (b i))) (sharp i)
  change timeDerivAt gt t₀ x (A (A (b i))) (sharp i) =
    -2 * g.ricciAt x (A (A (b i))) (sharp i) +
      (2 / (3 : ℝ)) * meanScalar g *
        g.inner x (A (A (b i))) (sharp i) at hEq
  change -timeDerivAt gt t₀ x (A (A (b i))) (sharp i) =
    2 * b.coord i (((A ∘ₗ A) ∘ₗ A) (b i)) -
      (2 / 3 : ℝ) * meanScalar g *
        b.coord i ((A ∘ₗ A) (b i))
  rw [hEq]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    coord_eq_inner_metricDualVectorAt_of_basis
      (g := g) (x := x) (b := b),
    coord_eq_inner_metricDualVectorAt_of_basis
      (g := g) (x := x) (b := b)]
  rw [← g.inner_ricciEndoAt x (A (A (b i))) (sharp i)]
  simp only [LinearMap.comp_apply]
  ring

set_option maxHeartbeats 4000000 in
/-- The reaction/motion trace assembled from the actual normalized metric
motion and the lower-Ricci evolution is Hamilton's cubic polynomial together
with the exact normalization correction `-(4/3) r |Ric|^2`. -/
theorem
    ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hFlow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hRicci : SatisfiesRicciEvolutionAt gt t₀ x) :
    ricciEvolutionPinchingReactionMotionTraceAt
        (metricRaiseDerivAt gt t₀ x hgt) hRicci rfl =
      (gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x -
        (4 / 3 : ℝ) * meanScalar (gt t₀) *
          (gt t₀).ricciNormSqAt x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
  let δRic3 : TM x → TM x → ℝ :=
    fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
  let hRic3 : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
    SatisfiesRicciEvolutionAt.reaction3
      (gt := gt) (t₀ := t₀) (x := x) hRicci rfl
  let K : TM x →L[ℝ] TM x :=
    ((metricRaiseDerivAt gt t₀ x hgt).comp
      (g.ricciDualContinuousAt x)).comp
      (g.ricciEndoContinuousAt x)
  let L : TM x →L[ℝ] TM x :=
    ((g.metricRaiseContinuousAt x).comp
      (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
        (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
      (g.ricciEndoContinuousAt x)
  have hSplit :
      (((metricRaiseDerivAt gt t₀ x hgt).comp
            (g.ricciDualContinuousAt x) +
          (g.metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
          (g.ricciEndoContinuousAt x)) = K + L := by
    ext v
    simp [K, L]
  have hTraceSplit :
      LinearMap.trace ℝ (TM x)
          ((((metricRaiseDerivAt gt t₀ x hgt).comp
                (g.ricciDualContinuousAt x) +
              (g.metricRaiseContinuousAt x).comp
                (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                  (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
              (g.ricciEndoContinuousAt x)).toLinearMap) =
        LinearMap.trace ℝ (TM x) K.toLinearMap +
          LinearMap.trace ℝ (TM x) L.toLinearMap := by
    rw [hSplit]
    exact map_add (LinearMap.trace ℝ (TM x)) K.toLinearMap L.toLinearMap
  have hTraceK :
      LinearMap.trace ℝ (TM x) K.toLinearMap =
        2 * g.ricciCubicTraceAt x -
          (2 / 3 : ℝ) * meanScalar g * g.ricciNormSqAt x := by
    simpa [g, K] using
      trace_metricRaiseDeriv_ricciDual_comp_ricciEndo_eq_two_cubic_sub_normalization
        (gt := gt) (t₀ := t₀) (x := x) hgt hFlow
  have hTraceL :
      LinearMap.trace ℝ (TM x) L.toLinearMap =
        metricVariationRicciPairingAt g
          (fun y : M ↦ fun u w : TM y ↦
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
      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
          - 2 * (gt t₀).scalarGradNormSqAt x
          + 4 * (gt t₀).scalarAt x * (gt t₀).ricciNormSqAt x
          - (4 / 3 : ℝ) * meanScalar (gt t₀) *
              (gt t₀).scalarAt x ^ 2 =
        (((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
              + 2 * (gt t₀).ricciNormSqAt x
              - (2 / 3 : ℝ) * meanScalar (gt t₀) *
                  (gt t₀).scalarAt x) * (gt t₀).scalarAt x
          + (gt t₀).scalarAt x *
            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
              + 2 * (gt t₀).ricciNormSqAt x
              - (2 / 3 : ℝ) * meanScalar (gt t₀) *
                  (gt t₀).scalarAt x)) := by
    rw [hsq_lap]
    simp [ClosedSmoothRiemannianMetric.scalarGradNormSqAt]
    ring
  rw [htarget]
  simpa [pow_two] using hprod

/-- The complete proof-free reaction in the normalized three-dimensional
traceless-Ricci energy equation. -/
noncomputable def normalizedTracelessRicciEvolutionReactionAt
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) : ℝ :=
  -2 * covRicciNormSqAt g x
    + (2 / 3 : ℝ) * g.scalarGradNormSqAt x
    + g.pinchingTracelessRicciReactionTrace3At x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x)
    - (4 / 3 : ℝ) * meanScalar g * g.tracelessRicciNormSqAt x

/-- The contracted-Bianchi estimate automatically makes the entire gradient
part of the normalized traceless-Ricci reaction nonpositive.  Consequently
the only coercivity obligation is the displayed algebraic cubic bound. -/
theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (rate : ℝ)
    (hCubic :
      g.pinchingTracelessRicciReactionTrace3At x
          (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤
        ((4 / 3 : ℝ) * meanScalar g - rate) *
          g.tracelessRicciNormSqAt x) :
    normalizedTracelessRicciEvolutionReactionAt g x ≤
      -rate * g.tracelessRicciNormSqAt x := by
  have hGradient := g.scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x
  unfold normalizedTracelessRicciEvolutionReactionAt
  linarith

/-- A convenient stronger sufficient condition: a nonpositive cubic
traceless reaction and a normalization rate at least `rate` imply the exact
reaction domination consumed by the decay theorem. -/
theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_nonpos
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (rate : ℝ)
    (hCubic :
      g.pinchingTracelessRicciReactionTrace3At x
          (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤ 0)
    (hRate : rate ≤ (4 / 3 : ℝ) * meanScalar g) :
    normalizedTracelessRicciEvolutionReactionAt g x ≤
      -rate * g.tracelessRicciNormSqAt x := by
  apply
    normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
  have hU := g.tracelessRicciNormSqAt_nonneg x (by norm_num)
  have hCoefficient :
      0 ≤ (4 / 3 : ℝ) * meanScalar g - rate := by
    linarith
  exact hCubic.trans (mul_nonneg hCoefficient hU)

set_option maxHeartbeats 12000000 in
/-- An actual normalized Ricci-flow slice with joint `C³` metric entries and
the normalized Hamilton scalar equation satisfies the exact
`Laplacian + explicit reaction` evolution for `|Ric°|²`.  No lower-Ricci,
inverse-metric, or traceless-energy derivative witness remains. -/
theorem
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_scalarEvolution
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hScalar : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ x) :
    HasDerivAt (fun t ↦ (gt t).tracelessRicciNormSqAt x)
      ((gt t₀).laplacianAt
          (fun y : M ↦ (gt t₀).tracelessRicciNormSqAt y) x
        + normalizedTracelessRicciEvolutionReactionAt (gt t₀) x) t₀ := by
  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
  let htime : TimeDifferentiableAt gt t₀ x :=
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint x).of_le (by norm_num))
  let raise' := metricRaiseDerivAt gt t₀ x htime
  let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
    satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three
      hFlow hJoint
  change HasDerivAt (fun t ↦ (gt t).tracelessRicciNormSqAt x)
    (g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
      + normalizedTracelessRicciEvolutionReactionAt g x) t₀
  have hRaise :
      HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ :=
    hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
      hFlow hEntries y
  have hNorm2 : ∀ y : M,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2
      (fun z : M ↦ g.ricciNormSqAt z) y := fun y ↦
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g y (hRicC2 y)
  have hScalar2 : ∀ y : M,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2
      (fun z : M ↦ g.scalarAt z) y := fun y ↦
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries y
  have hScalarSq2 : ∀ y : M,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2
      (fun z : M ↦ g.scalarAt z ^ 2) y := fun y ↦ by
    simpa [pow_two] using (hScalar2 y).smul (hScalar2 y)
  have hPairDiff : ∀ w : TM x,
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
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
  have hScalarSqDiff : ∀ y : M,
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z : M ↦ g.scalarAt z ^ 2) y := fun y ↦
    (hScalarSq2 y).mdifferentiableAt two_ne_zero
  have hScalarSqGrad :
      MDifferentiableAt I ((I).prod (modelWithCornersSelf ℝ E))
        (T% (g.gradient (fun z : M ↦ g.scalarAt z ^ 2))) x :=
    g.mdifferentiableAt_gradient (hScalarSq2 x)
  let R : ℝ := g.scalarAt x
  let N : ℝ := g.ricciNormSqAt x
  let r : ℝ := meanScalar g
  let lapN : ℝ := g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
  let lapR2 : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y ^ 2) x
  let lapU : ℝ :=
    g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
  let A : ℝ := covRicciNormSqAt g x
  let S : ℝ := g.scalarGradNormSqAt x
  let cubicReaction : ℝ :=
    g.pinchingRicciNormReactionMotionTraceCubicAt x
  let actualReaction : ℝ :=
    ricciEvolutionPinchingReactionMotionTraceAt raise' hRicci rfl
  let Nrhs : ℝ :=
    lapN - 2 * A + cubicReaction - (4 / 3 : ℝ) * r * N
  let R2rhs : ℝ :=
    lapR2 - 2 * S + 4 * R * N - (4 / 3 : ℝ) * r * R ^ 2
  have hNraw :
      HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x)
        (lapN - 2 * A + actualReaction) t₀ := by
    simpa [g, lapN, A, actualReaction,
      ricciEvolutionPinchingReactionMotionTraceAt] using
      hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
        (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
        hRaise hRicci rfl (hNorm2 x) hPairDiff hRicSecond
  have hActualReaction :
      actualReaction = cubicReaction - (4 / 3 : ℝ) * r * N := by
    simpa [actualReaction, cubicReaction, r, N, raise'] using
      ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization
        htime (hFlow x) hRicci
  have hN :
      HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x) Nrhs t₀ := by
    rw [hActualReaction] at hNraw
    change HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x)
      (lapN - 2 * A + cubicReaction - (4 / 3 : ℝ) * r * N) t₀
    convert hNraw using 1
    all_goals ring
  have hR2 :
      HasDerivAt (fun t ↦ (gt t).scalarAt x ^ 2) R2rhs t₀ := by
    simpa [g, R, N, r, lapR2, S, R2rhs] using
      hasDerivAt_scalarAt_sq_of_satisfiesNormalizedHamiltonScalarEvolutionAt
        (gt := gt) (t₀ := t₀) (x := x) hScalar hScalar2
  have hU :
      HasDerivAt (fun t ↦ (gt t).tracelessRicciNormSqAt x)
        (Nrhs - R2rhs / (3 : ℝ)) t₀ :=
    ClosedSmoothRiemannianMetric.hasDerivAt_tracelessRicciNormSqAt_of_ricciNormSq_and_scalar_sq
      hN hR2
  have hRicNormDiff : ∀ y : M,
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z : M ↦ g.ricciNormSqAt z) y := fun y ↦
    (hNorm2 y).mdifferentiableAt two_ne_zero
  have hRicNormGrad :
      MDifferentiableAt I ((I).prod (modelWithCornersSelf ℝ E))
        (T% (g.gradient (fun z : M ↦ g.ricciNormSqAt z))) x :=
    g.mdifferentiableAt_gradient (hNorm2 x)
  have hLapU :
      lapU = lapN - (2 / 3 : ℝ) * R * lapR - (2 / 3 : ℝ) * S := by
    simpa [g, lapU, lapN, lapR, R, S] using
      g.laplacianAt_tracelessRicciNormSqAt_eq
        x hRicNormDiff hRicNormGrad hScalar2 hScalarSqDiff hScalarSqGrad
  have hLapR2 : lapR2 = 2 * R * lapR + 2 * S := by
    simpa [g, lapR2, R, lapR, S,
      ClosedSmoothRiemannianMetric.scalarGradNormSqAt] using
      g.laplacianAt_sq (f := fun y : M ↦ g.scalarAt y) (x := x) hScalar2
  have htarget :
      Nrhs - R2rhs / (3 : ℝ) =
        lapU + normalizedTracelessRicciEvolutionReactionAt g x := by
    dsimp [Nrhs, R2rhs]
    rw [hLapU, hLapR2]
    unfold normalizedTracelessRicciEvolutionReactionAt
      ClosedSmoothRiemannianMetric.pinchingTracelessRicciReactionTrace3At
      ClosedSmoothRiemannianMetric.pinchingScalarReactionAt
      ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt
    ring
  convert hU using 1
  exact htarget.symm

/-- The assembled Lichnerowicz package supplies the remaining scalar equation,
so normalized flow plus joint `C³` slice data give the exact explicit
traceless-Ricci evolution with no pointwise evolution premise. -/
theorem
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_globalLichnerowicz
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
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
      (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt 0) * Real.exp ((-rate) * t.1) := by
  apply
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_reaction_domination_of_normalizedFlow_jointMetricEntries_Ici
      gt hFlow hJointMetricEntries
      (fun t x ↦ normalizedTracelessRicciEvolutionReactionAt (gt t) x)
  · intro x t ht
    exact
      hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_globalLichnerowicz
        (fun y ↦ hFlow t ht y) (fun y ↦ hJointMetricEntries t ht y)
        hLichnerowicz
  · exact hReaction

/-- With global joint `C³` entries, the preceding pointwise decay theorem is
fully automatic from normalized flow and the explicit reaction bound. -/
theorem
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJointMetricEntries : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    {rate : ℝ}
    (hReaction : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
        -rate * (gt t).tracelessRicciNormSqAt x) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt 0) * Real.exp ((-rate) * t.1) := by
  exact
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_actualNormalizedReaction_domination_of_normalizedFlow_jointMetricEntries_Ici
      gt hFlow
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
        hJointMetricEntries)
      (fun t _ht ↦ hJointMetricEntries t) hReaction

/-- A positive coercive bound for the explicit normalized reaction implies
finite total forward traceless-Ricci energy, without a raw `hEvolution`
argument. -/
theorem
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hJointMetricEntries : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    {rate : ℝ} (hrate : 0 < rate)
    (hReaction : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
        -rate * (gt t).tracelessRicciNormSqAt x) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  apply
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_reaction_domination_of_normalizedFlow_jointMetricEntries_Ici
      gt hFlow hVolumeVariation hMeasurable hJointMetricEntries
      (fun t x ↦ normalizedTracelessRicciEvolutionReactionAt (gt t) x)
      hrate
  · intro x t ht
    exact
      hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_globalLichnerowicz
        (fun y ↦ hFlow t ht y) (fun y ↦ hJointMetricEntries t ht y)
        hLichnerowicz
  · exact hReaction

/-- Global joint `C³` entries also remove the Lichnerowicz package argument
from the finite-energy consequence. -/
theorem
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    (hJointMetricEntries : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    {rate : ℝ} (hrate : 0 < rate)
    (hReaction : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
        -rate * (gt t).tracelessRicciNormSqAt x) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  exact
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_jointMetricEntries_Ici
      gt hFlow hVolumeVariation hMeasurable
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
        hJointMetricEntries)
      (fun t _ht ↦ hJointMetricEntries t) hrate hReaction

end Poincare
