import Poincare.Global.MetricFlowJointIteratedConnectionRegularity
import Poincare.Global.DeltaGammaFieldRegularity
import Poincare.Global.RicciFlowScalarRegularity

/-!
# Ricci-tensor evolution from joint metric regularity

The closed Ricci-tensor variation theorem was previously exposed through a
collection of connection, mixed-partial, and second-spatial-regularity
hypotheses.  Joint `C³` regularity of the metric entries supplies all of the
time/connection hypotheses.  On a genuine Ricci-flow slice it also makes
`Ric = -½ ∂ₜg` entrywise `C²`, which supplies the remaining curvature
commutation regularity.

Thus the standard tensor evolution equation

`d/dt Ric = Δ Ric + 2 Rm(Ric) - Ric² - (Ric²)ᵀ`

follows from the same natural assembled-flow data already used for Hamilton's
scalar evolution.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
A genuine closed Ricci-flow slice with globally joint `C³` canonical metric
entries satisfies Hamilton's Ricci-tensor evolution equation at every point.

No separate `MetricFlowRegularAt`, `DeltaGammaEntryDerivativeBridgeAt`, or
Ricci/scalar second-regularity premise remains: each is reconstructed from the
joint metric-entry hypothesis and the Ricci-flow equation.
-/
theorem satisfiesRicciEvolutionAt_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
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
  have hFlowNear :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
          ClosedRicciFlowExtensionRegularAt gt t₀ y :=
    Eventually.of_forall
      (global_isClosedRicciFlowSolutionAt_and_extensionRegularAt
        gt t₀ hFlow)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField (gt t₀)) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_ricciFlow
      hFlow hEntries y
  have hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (ricciVariationField (gt t₀)) x :=
    covTensor2DerivExtDifferentiableAt_of_extSecond
      (g := gt t₀) (h := ricciVariationField (gt t₀)) (x := x)
      (covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two (hRicC2 x))
      (fun y ↦ covTensor2ExtDifferentiableAt_of_contMDiffAt_two (hRicC2 y))
      (tensor2AddLeft_ricciVariationField (gt t₀))
      (tensor2SMulLeft_ricciVariationField (gt t₀))
      (tensor2AddRight_ricciVariationField (gt t₀))
      (tensor2SMulRight_ricciVariationField (gt t₀))
  have hScalar₂ :
      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t₀).scalarAt y) x :=
    scalarAt_contMDiffAt_two_of_ricciFlow hFlow hEntries x
  have hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ (gt t₀).scalarAt z) y
            (extend E w y)) x := by
    intro w
    have hW :
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E w)) x := by
      simpa using (mdifferentiableAt_extend I E w)
    exact CovariantDerivative.mdiffAt_extDerivFun_apply hScalar₂ hW
  exact satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity
    (gt := gt) (t₀ := t₀) (x := x)
    (hReg x) hgt hExt hNear hBridge hSecond hFlowNear
    hRicSecond (hRicC2 x) hScalar₂ hScalarExt₂

end Poincare
