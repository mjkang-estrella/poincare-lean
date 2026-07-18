import Poincare.Global.DeTurckLocalFrameRegularity

/-!
# Regularity-closed DeTurck gauged-flow predicate

The concrete DeTurck vector field is now unconditionally `C²`.  Consequently
the gauged-flow predicate is equivalent to its Levi-Civita and evolution
equations; no separate vector-field regularity premise remains.
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
local notation "TM" => (TangentSpace I : M → Type _)

/-- The concrete gauged-flow predicate is constructed from the two actual
equations, with DeTurck-field regularity discharged internally. -/
theorem isDeTurckGaugedFlowAt_of_equations
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hlevi : ∀ t : ℝ,
      CovariantDerivative.IsLeviCivitaAt
        (fun y ↦ (gt t).inner y) (gt t).leviCivita x)
    (hflow : ∀ {Z : ∀ y : M, TM y},
      ClosedC2TangentField (n := n) (M := M) Z →
      ∀ (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
        (w : TM x),
        deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
          -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w +
            lieDerivMetricAt (gt t₀) (deTurckVectorField gt bg t₀)
              x (Z x) w) :
    IsDeTurckGaugedFlowAt gt bg t₀ x := by
  refine ⟨hlevi, ?_, hflow⟩
  exact deTurckVectorFieldRegularAt_holds gt bg t₀

/-- With the regularity theorem available, a concrete gauged flow is exactly
its Levi-Civita clause together with the Ricci--DeTurck evolution equation. -/
theorem isDeTurckGaugedFlowAt_iff_equations
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    IsDeTurckGaugedFlowAt gt bg t₀ x ↔
      (∀ t : ℝ,
        CovariantDerivative.IsLeviCivitaAt
          (fun y ↦ (gt t).inner y) (gt t).leviCivita x) ∧
      ∀ {Z : ∀ y : M, TM y},
        ClosedC2TangentField (n := n) (M := M) Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
          (w : TM x),
          deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
            -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w +
              lieDerivMetricAt (gt t₀) (deTurckVectorField gt bg t₀)
                x (Z x) w := by
  constructor
  · intro h
    exact ⟨h.leviCivita, h.flow⟩
  · rintro ⟨hlevi, hflow⟩
    exact isDeTurckGaugedFlowAt_of_equations gt bg t₀ x hlevi hflow

end Poincare
