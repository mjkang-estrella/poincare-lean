import Poincare.Global.Curvature

/-!
# Closed Ricci-flow wrapper

This module packages the pointwise Ricci-flow equation for a time-family of
`ClosedSmoothRiemannianMetric`s.  The connection used at time `t` is the
canonical Levi-Civita connection `(gt t).leviCivita`, i.e. the closed
specialization of the global Koszul construction.
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

/-- A `C²` tangent field in the standard closed smooth model. -/
abbrev ClosedC2TangentField
    (Z : ∀ y : M, TM y) : Prop :=
  ContMDiff I ((I).prod 𝓘(ℝ, E)) 2
    (fun y : M => (Z y : TotalSpace E TM))

/--
The pointwise Ricci-flow solution condition for a time-family of closed smooth
Riemannian metrics, using the canonical Levi-Civita connection at each time.
-/
def IsClosedRicciFlowSolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  CovariantDerivative.IsRicciFlowSolutionAt
    (fun t y ↦ (gt t).inner y) (fun t ↦ (gt t).leviCivita) t₀ x

/-- Unfold the closed wrapper to the underlying pointwise Ricci-flow PDE. -/
@[simp] theorem isClosedRicciFlowSolutionAt_iff
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    IsClosedRicciFlowSolutionAt gt t₀ x ↔
      CovariantDerivative.IsRicciFlowSolutionAt
        (fun t y ↦ (gt t).inner y) (fun t ↦ (gt t).leviCivita) t₀ x :=
  Iff.rfl

private theorem closedLeviCivitaConnection_eq_metricFlowConnection
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) :
    CovariantDerivative.leviCivitaConnection ((gt t).inner)
      (fun y v w ↦ (gt t).inner_symm y v w)
      (fun y v hv ↦ LeviCivitaExistence.metric_nondegenerate (gt t) y v hv)
      (fun _ _ _ hA hB ↦ (gt t).metric_pairing_mdiffAt hA hB) =
        (gt t).leviCivita := by
  unfold ClosedSmoothRiemannianMetric.leviCivita
    LeviCivitaExistence.closedLeviCivitaConnection
  rfl

/--
Specialize the Koszul metric-flow constructor to closed smooth metrics.

The symmetry, nondegeneracy, and pairing regularity hypotheses required by
`CovariantDerivative.isRicciFlowSolutionAt_of_metric` are discharged from the
metric data of each `(gt t)`.  The only remaining hypothesis is the genuine
pointwise Ricci-flow equation for the canonical connection at `(t₀, x)`.
-/
theorem isClosedRicciFlowSolutionAt_of_metric
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    {t₀ : ℝ} {x : M}
    (hflow :
      ∀ {Z : ∀ y : M, TM y}, ClosedC2TangentField Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
          (w : TM x),
          deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
            -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w) :
    IsClosedRicciFlowSolutionAt gt t₀ x := by
  let hgsymm : ∀ (t : ℝ) (y : M) (v w : TM y),
      (gt t).inner y v w = (gt t).inner y w v :=
    fun t y v w ↦ (gt t).inner_symm y v w
  let hgnd : ∀ (t : ℝ) (y : M) (v : TM y),
      (∀ w, (gt t).inner y v w = 0) → v = 0 :=
    fun t y v hv ↦ LeviCivitaExistence.metric_nondegenerate (gt t) y v hv
  let hP : ∀ (t : ℝ) (x : M) (A B : ∀ y : M, TM y),
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
          (fun y : M => (A y : TotalSpace E TM)) x →
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
          (fun y : M => (B y : TotalSpace E TM)) x →
        MDifferentiableAt I 𝓘(ℝ)
          (fun y ↦ (gt t).inner y (A y) (B y)) x :=
    fun t _ _ _ hA hB ↦ (gt t).metric_pairing_mdiffAt hA hB
  have hconn_t₀ :
      CovariantDerivative.leviCivitaConnection ((gt t₀).inner)
        (hgsymm t₀) (hgnd t₀) (hP t₀) = (gt t₀).leviCivita := by
    exact closedLeviCivitaConnection_eq_metricFlowConnection gt t₀
  have sol : CovariantDerivative.IsRicciFlowSolutionAt
      (fun t y ↦ (gt t).inner y)
      (fun t ↦ CovariantDerivative.leviCivitaConnection ((gt t).inner)
        (hgsymm t) (hgnd t) (hP t)) t₀ x := by
    refine CovariantDerivative.isRicciFlowSolutionAt_of_metric
      (gt := fun t y ↦ (gt t).inner y) hgsymm hgnd hP ?_
    intro Z hZ hreg w
    simpa [hconn_t₀] using hflow (Z := Z) hZ
      (by simpa [hconn_t₀] using hreg) w
  have hconn :
      (fun t ↦ CovariantDerivative.leviCivitaConnection ((gt t).inner)
        (hgsymm t) (hgnd t) (hP t)) = fun t ↦ (gt t).leviCivita := by
    funext t
    exact closedLeviCivitaConnection_eq_metricFlowConnection gt t
  simpa [IsClosedRicciFlowSolutionAt, hconn] using sol

/-- A Ricci-flat closed metric is a static closed Ricci-flow solution. -/
theorem isClosedRicciFlowSolutionAt_const_of_ricciFlat
    (g : ClosedSmoothRiemannianMetric n M) {x : M}
    (hric : ∀ {Z : ∀ y : M, TM y}, ClosedC2TangentField Z →
      ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x) (w : TM x),
        CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0)
    (t₀ : ℝ) :
    IsClosedRicciFlowSolutionAt (fun _ ↦ g) t₀ x := by
  have hLC : CovariantDerivative.IsLeviCivitaAt g.inner g.leviCivita x :=
    ⟨g.leviCivita_metricCompatibleAt x, g.leviCivita_torsionFreeAt x⟩
  simpa [IsClosedRicciFlowSolutionAt] using
    (CovariantDerivative.isRicciFlowSolutionAt_const_of_ricciFlat
      (g₀ := fun y ↦ g.inner y) (cov := g.leviCivita) (x := x) hLC
      (fun {Z} hZ hreg w ↦ hric (Z := Z) hZ hreg w) t₀)

end Poincare
