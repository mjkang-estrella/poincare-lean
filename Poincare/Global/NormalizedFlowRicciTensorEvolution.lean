import Poincare.Global.MetricFlowJointRicciTensorEvolution
import Poincare.Global.NormalizedFlowJointPinchingRegularity

/-!
# Ricci-tensor evolution for normalized Ricci flow

The lower Ricci tensor is unchanged by a spatially constant rescaling of the
metric.  Infinitesimally, the normalization term

`(2 / n) * meanScalar(g) * g`

therefore contributes nothing to the lower-Ricci evolution equation.  This
file makes that cancellation explicit at the level of the repository's
second-covariant-derivative variation formula and derives Hamilton's usual
lower-Ricci evolution from an actual normalized Ricci flow with joint `C³`
metric entries.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Covariant differentiation is additive in the tensor field. -/
theorem covTensor2DerivAt_add_fields
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hh : CovTensor2ExtDifferentiableAt h x)
    (hk : CovTensor2ExtDifferentiableAt k x)
    (v p q : TM x) :
    covTensor2DerivAt g (fun y a b ↦ h y a b + k y a b) x v p q =
      covTensor2DerivAt g h x v p q +
        covTensor2DerivAt g k x v p q := by
  have hentry :
      (fun y : M ↦
          h y (extend E p y) (extend E q y) +
            k y (extend E p y) (extend E q y)) =
        (fun y : M ↦ h y (extend E p y) (extend E q y)) +
          fun y : M ↦ k y (extend E p y) (extend E q y) := by
    rfl
  unfold covTensor2DerivAt
  rw [hentry, extDerivFun_add (hh p q) (hk p q)]
  simp only [ContinuousLinearMap.add_apply, sub_eq_add_neg, neg_add_rev]
  abel

/-- A spatially constant multiple of the metric is covariantly constant. -/
theorem covTensor2DerivAt_const_smul_metric_eq_zero
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (x : M)
    (v p q : TM x) :
    covTensor2DerivAt g (fun y a b ↦ c * g.inner y a b) x v p q = 0 := by
  have hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun _ : M ↦ c) x := mdifferentiableAt_const
  simpa using
    (covTensor2DerivAt_scalar_metric
      (g := g) (f := fun _ : M ↦ c) (x := x) hf v p q)

/-- Canonical entries of a constant metric multiple are differentiable. -/
theorem covTensor2ExtDifferentiableAt_const_smul_metric
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (x : M) :
    CovTensor2ExtDifferentiableAt (fun y a b ↦ c * g.inner y a b) x := by
  intro p q
  have hmetric := metricExtContMDiffAt_two g x p q
  simpa using
    (mdifferentiableAt_const.mul
      (hmetric.mdifferentiableAt two_ne_zero))

/-- Adding a spatially constant metric multiple does not change a second
covariant derivative of a tensor. -/
theorem covTensor2SecondDerivAt_add_const_smul_metric_eq
    (g : ClosedSmoothRiemannianMetric n M)
    {h : ∀ y : M, TM y → TM y → ℝ}
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (c : ℝ) (x : M) (u v p q : TM x) :
    covTensor2SecondDerivAt g
        (fun y a b ↦ h y a b + c * g.inner y a b) x u v p q =
      covTensor2SecondDerivAt g h x u v p q := by
  have hpath :
      (fun y : M ↦
          covTensor2DerivAt g
            (fun z a b ↦ h z a b + c * g.inner z a b) y
            (extend E v y) (extend E p y) (extend E q y)) =
        fun y : M ↦
          covTensor2DerivAt g h y
            (extend E v y) (extend E p y) (extend E q y) := by
    funext y
    rw [covTensor2DerivAt_add_fields g (hDiff y)
      (covTensor2ExtDifferentiableAt_const_smul_metric g c y)]
    rw [covTensor2DerivAt_const_smul_metric_eq_zero]
    ring
  unfold covTensor2SecondDerivAt
  rw [hpath]
  rw [covTensor2DerivAt_add_fields g (hDiff x)
    (covTensor2ExtDifferentiableAt_const_smul_metric g c x)]
  rw [covTensor2DerivAt_add_fields g (hDiff x)
    (covTensor2ExtDifferentiableAt_const_smul_metric g c x)]
  rw [covTensor2DerivAt_add_fields g (hDiff x)
    (covTensor2ExtDifferentiableAt_const_smul_metric g c x)]
  simp only [covTensor2DerivAt_const_smul_metric_eq_zero]
  ring

/-- At fixed time, the normalized Ricci-flow speed has the same second
covariant derivative as `-2 Ric`; the normalization term is a spatially
constant multiple of the metric. -/
theorem covTensor2SecondDerivAt_normalizedRicciFlowRHSAt_eq_negTwoRicci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v p q : TM x) :
    covTensor2SecondDerivAt g
        (fun y a b ↦ normalizedRicciFlowRHSAt g y a b) x u v p q =
      covTensor2SecondDerivAt g (negTwoRicciVariationField g) x u v p q := by
  let c : ℝ := (2 / (n : ℝ)) * meanScalar g
  have hfield :
      (fun y : M ↦ fun a b : TM y ↦ normalizedRicciFlowRHSAt g y a b) =
        fun y : M ↦ fun a b : TM y ↦
          negTwoRicciVariationField g y a b + c * g.inner y a b := by
    funext y a b
    simp [normalizedRicciFlowRHSAt, negTwoRicciVariationField,
      ricciVariationField, c]
  rw [hfield]
  apply covTensor2SecondDerivAt_add_const_smul_metric_eq
  intro y a b
  have hc : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun _ : M ↦ (-2 : ℝ)) y := mdifferentiableAt_const
  change MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
    (fun z : M ↦ (-2 : ℝ) * g.ricciAt z (extend E a z) (extend E b z)) y
  exact hc.mul
    (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y a b)

/-- The full contracted second-variation formula likewise discards the
normalization term. -/
theorem deltaRicciSecondDerivContractionAt_normalizedRicciFlowRHSAt_eq_negTwoRicci
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u w : TM x) :
    deltaRicciSecondDerivContractionAt g
        (fun y a b ↦ normalizedRicciFlowRHSAt g y a b) x u w =
      deltaRicciSecondDerivContractionAt g
        (negTwoRicciVariationField g) x u w := by
  classical
  unfold deltaRicciSecondDerivContractionAt
  simp_rw [covTensor2SecondDerivAt_normalizedRicciFlowRHSAt_eq_negTwoRicci]

/-- A normalized Ricci-flow slice with joint `C³` metric entries satisfies
the usual Hamilton lower-Ricci tensor evolution equation.  No independent
Ricci-tensor evolution witness remains. -/
theorem satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3) :
    SatisfiesRicciEvolutionAt gt t₀ x := by
  have hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y := fun y ↦
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint y).of_le (by norm_num))
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hReg : ∀ y : M, MetricFlowRegularAt gt t₀ y := fun y ↦
    metricFlowRegularAt_of_metricEntriesJointContDiffAt_three
      (x := y) hJoint
  have hNear :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦
                  (gt t).inner z (extend E b z) (extend E c z)) y a)
            (extDerivFun
              (fun z : M ↦
                timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀) :=
    eventually_metricFlowRegularAt_and_mixed_of_jointContDiffAt_two
      (Eventually.of_forall hReg)
      (Eventually.of_forall fun y ↦ (hJoint y).of_le (by norm_num))
  have hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦
                (gt t).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦
              timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀ :=
    metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
      ((hJoint x).of_le (by norm_num))
  have hTraceEntries : ∀ y : M,
      TimeVariationTraceEntriesExtContMDiffAt gt t₀ y 2 := fun y ↦
    ⟨hEntries y, metricExtContMDiffAt_two (gt t₀) y⟩
  have hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x :=
    covTensor2DerivExtDifferentiableAt_timeDeriv_of_global_entries
      hgt hTraceEntries
  have hConn : ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y :=
    (hReg x).connection
  have hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x :=
    deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt
      (deltaGammaFieldMDifferentiableAt_of_metricEntriesJointContDiffAt_three
        (hJoint x) hConn)
  have hCurvComm : RicciSecondDerivCurvatureCommutationAt (gt t₀) x :=
    RicciSecondDerivCurvatureCommutationAt.canonical (gt t₀) x
  have hCyclic :
      ∀ u v w z : TM x,
        closedCurvatureCovDerivAt (gt t₀) x v u w z
          + closedCurvatureCovDerivAt (gt t₀) x u w v z
          + closedCurvatureCovDerivAt (gt t₀) x w v u z = 0 := by
    exact (eventually_closed_cyclic_second_bianchi (g := gt t₀) x).self_of_nhds
  have hComm : RicciSecondDerivCommutationAt (gt t₀) x :=
    RicciSecondDerivCommutationAt.of_closed_bianchi
      (g := gt t₀) (x := x)
      (closedRicciDerivativeExpansionAt_canonical (g := gt t₀) x)
      hCyclic hCurvComm
  apply satisfiesRicciEvolutionAt_of_secondDerivCommutation
    (gt := gt) (t₀ := t₀) (x := x) _ hComm
  intro u w
  have hDeriv := ricciVariation_eq_deltaGamma_contractions'
    (gt := gt) (t₀ := t₀) (x := x) (hReg x) u w
  have hDelta :
      deltaRicciAt gt t₀ x u w =
        deltaRicciSecondDerivContractionAt
          (gt t₀) (timeDerivAt gt t₀) x u w :=
    deltaRicciAt_eq_secondDerivContractionAt
      (gt := gt) (t₀ := t₀) (x := x)
      (hReg x) hgt hExt hNear hBridge hSecond u w
  have hSpeed :
      ∀ᶠ y in nhds x, ∀ a b : TM y,
        timeDerivAt gt t₀ y a b =
          normalizedRicciFlowRHSAt (gt t₀) y a b :=
    Eventually.of_forall fun y a b ↦
      isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
        (gt := gt) (t₀ := t₀) (x := y) (hFlow y) a b
  have hCongr :
      deltaRicciSecondDerivContractionAt
          (gt t₀) (timeDerivAt gt t₀) x u w =
        deltaRicciSecondDerivContractionAt
          (gt t₀)
          (fun y a b ↦ normalizedRicciFlowRHSAt (gt t₀) y a b)
          x u w :=
    deltaRicciSecondDerivContractionAt_congr_of_eventuallyEq
      (gt t₀) hSpeed u w
  have hScale :=
    deltaRicciSecondDerivContractionAt_normalizedRicciFlowRHSAt_eq_negTwoRicci
      (gt t₀) x u w
  apply hDeriv.congr_deriv
  rw [hDelta, hCongr, hScale]

end Poincare
