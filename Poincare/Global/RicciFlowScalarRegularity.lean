import Poincare.Global.ScalarVariation

/-!
# Scalar regularity from a smooth Ricci-flow slice

On a genuine Ricci-flow time slice, `∂ₜg = -2 Ric`.  Thus C² spatial
regularity of the time-variation entries immediately gives C² Ricci entries.
The existing inverse-Gram trace theorem then gives C² scalar curvature.  This
removes a separate scalar-curvature regularity premise from the Hamilton
scalar-evolution assembly.
-/

noncomputable section

open Bundle FiberBundle
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

/-- Under the global pointwise Ricci-flow equation, C² time-variation entries
give C² Ricci entries. -/
theorem ricciVariationField_extContMDiffAt_two_of_ricciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2)
    (x : M) :
    CovTensor2ExtContMDiffAt (ricciVariationField (gt t₀)) x 2 := by
  intro p q
  let H : M → ℝ := fun y ↦
    timeDerivAt gt t₀ y (extend E p y) (extend E q y)
  let R : M → ℝ := fun y ↦
    (gt t₀).ricciAt y (extend E p y) (extend E q y)
  have hH : ContMDiffAt I 𝓘(ℝ) 2 H x := by
    simpa [H, TimeVariationExtContMDiffAt,
      CovTensor2ExtContMDiffAt] using hEntries x p q
  have hscale : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (-1 / 2 : ℝ) * H y) x := by
    have hc : ContMDiffAt I 𝓘(ℝ) 2
        (fun _ : M ↦ (-1 / 2 : ℝ)) x := contMDiffAt_const
    exact hc.smul hH
  have heq : R = fun y : M ↦ (-1 / 2 : ℝ) * H y := by
    funext y
    have hEq :=
      isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt
        (gt := gt) (t₀ := t₀) (x := y)
        (hFlow y)
        (closedRicciFlowExtensionRegularAt_canonical gt t₀ y)
        (extend E p y) (extend E q y)
    change H y = -2 * R y at hEq
    rw [hEq]
    ring
  change ContMDiffAt I _ 2 R x
  rw [heq]
  exact hscale

/-- The metric trace of the preceding C² Ricci tensor is the actual scalar
curvature, hence scalar curvature is C² on the time slice. -/
theorem scalarAt_contMDiffAt_two_of_ricciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2)
    (x : M) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t₀).scalarAt y) x := by
  have hTraceEntries :
      TraceMetricVariationEntriesExtContMDiffAt
        (gt t₀) (ricciVariationField (gt t₀)) x 2 :=
    ⟨ricciVariationField_extContMDiffAt_two_of_ricciFlow
        hFlow hEntries x,
      metricExtContMDiffAt_two (gt t₀) x⟩
  have hTrace : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦
        traceMetricVariationAt (gt t₀) (ricciVariationField (gt t₀)) y) x :=
    traceMetricVariationAt_contMDiffAt_two_of_entries
      (g := gt t₀) (h := ricciVariationField (gt t₀)) (x := x)
      hTraceEntries (ricciVariationBilinForm (gt t₀))
      (by intro y p q; rfl)
  have hfun :
      (fun y : M ↦
        traceMetricVariationAt (gt t₀) (ricciVariationField (gt t₀)) y) =
      fun y : M ↦ (gt t₀).scalarAt y := by
    funext y
    exact traceMetricVariationAt_ricci (gt t₀) y
  simpa [hfun] using hTrace

/--
The canonical contracted-Bianchi one-form identity makes the Ricci divergence
entry differentiable as soon as scalar curvature is C².  Thus the
double-divergence linearity step does not need a separate Ricci-divergence
regularity premise.
-/
theorem ricciDivergenceOneForm_mdifferentiableAt_of_scalar_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {x : M}
    (hScalar₂ :
      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x)
    (w : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        tensorDivergenceOneFormAt g (ricciVariationField g) y
          (extend E w y)) x := by
  let f : M → ℝ := fun y ↦ g.scalarAt y
  let F : M → ℝ := fun y ↦
    extDerivFun f y (extend E w y)
  have hw :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E w)) x := by
    simpa using (mdifferentiableAt_extend I E w)
  have hF : MDifferentiableAt I 𝓘(ℝ) F x := by
    simpa [F, f] using
      CovariantDerivative.mdiffAt_extDerivFun_apply hScalar₂ hw
  have hhalf :
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ (1 / 2 : ℝ) * F y) x :=
    mdifferentiableAt_const.mul hF
  have heq :
      (fun y : M ↦
        tensorDivergenceOneFormAt g (ricciVariationField g) y
          (extend E w y)) =ᶠ[nhds x]
        fun y : M ↦ (1 / 2 : ℝ) * F y := by
    filter_upwards
      [eventually_closedContractedBianchiOneFormAt_canonical
        (g := g) (x := x)] with y hy
    simpa [F, f] using hy (extend E w y)
  exact hhalf.congr_of_eventuallyEq heq

/--
For a Ricci-flow slice with global C² variation entries, the Ricci divergence
regularity consumed by Hamilton scalar evolution is automatic.
-/
theorem ricciDivergenceOneForm_mdifferentiableAt_of_ricciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2)
    (x : M) (w : TM x) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦
        tensorDivergenceOneFormAt (gt t₀)
          (ricciVariationField (gt t₀)) y (extend E w y)) x :=
  ricciDivergenceOneForm_mdifferentiableAt_of_scalar_contMDiffAt_two
    (g := gt t₀)
    (scalarAt_contMDiffAt_two_of_ricciFlow hFlow hEntries x) w

end Poincare
