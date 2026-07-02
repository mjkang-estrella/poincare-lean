import Poincare.Global.Laplacian
import Poincare.Global.RicciNorm
import Poincare.Global.RicciFlow

/-!
# Closed-manifold scalar evolution statement

This module records the closed-manifold Hamilton scalar evolution equation in
terms of the current global vocabulary:
`scalarAt`, `laplacianAt`, `ricciNormSqAt`, and
`IsClosedRicciFlowSolutionAt`.

The full closed-manifold proof is intentionally not supplied here.  The
single-chart analogues already live in `ModelLaplacian.lean`; this file adds
the statement layer and a static Ricci-flat sanity instance.
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

/--
Hamilton's scalar evolution equation at a point of a time-family of closed
smooth Riemannian metrics.

The implicit regularity instance is exactly the one required by the existing
`scalarAt` and `ricciNormSqAt` wrappers for each time-slice.
-/
def SatisfiesHamiltonScalarEvolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  HasDerivAt (fun t ↦ (gt t).scalarAt x)
    ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
      2 * (gt t₀).ricciNormSqAt x) t₀

/-- Unfold the closed Hamilton scalar evolution statement. -/
@[simp] theorem satisfiesHamiltonScalarEvolutionAt_iff
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x ↔
      HasDerivAt (fun t ↦ (gt t).scalarAt x)
        ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
          2 * (gt t₀).ricciNormSqAt x) t₀ :=
  Iff.rfl

namespace ClosedSmoothRiemannianMetric

section StaticFlat

variable (g : ClosedSmoothRiemannianMetric n M)
variable [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]

/-- A vanishing Ricci bilinear form has zero raised Ricci endomorphism. -/
theorem ricciEndoAt_eq_zero_of_ricciAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.ricciEndoAt x = 0 := by
  ext u
  simp only [LinearMap.zero_apply]
  exact LeviCivitaExistence.metric_nondegenerate g x (g.ricciEndoAt x u) fun w ↦ by
    rw [g.inner_ricciEndoAt, hric u w]

/-- A vanishing Ricci bilinear form has zero pointwise squared Ricci norm. -/
theorem ricciNormSqAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.ricciNormSqAt x = 0 := by
  rw [g.ricciNormSqAt_eq_trace, g.ricciEndoAt_eq_zero_of_ricciAt_eq_zero hric]
  simp

/-- A vanishing Ricci bilinear form has zero scalar curvature. -/
theorem scalarAt_eq_zero_of_ricciAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.scalarAt x = 0 := by
  rw [g.scalarAt_eq_trace_ricciEndoAt, g.ricciEndoAt_eq_zero_of_ricciAt_eq_zero hric]
  simp

/--
If the Ricci bilinear form vanishes everywhere, then the scalar curvature
function is identically zero, so its Laplacian vanishes by `laplacianAt_const`.
-/
theorem laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero
    (hric : ∀ y : M, ∀ u w : TM y, g.ricciAt y u w = 0) (x : M) :
    g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 := by
  have hscalar :
      (fun y : M ↦ g.scalarAt y) = fun _ : M ↦ 0 := by
    funext y
    exact g.scalarAt_eq_zero_of_ricciAt_eq_zero (hric y)
  rw [hscalar]
  exact g.laplacianAt_const 0 x

/-- Along a time-constant metric family, scalar curvature has zero time derivative. -/
theorem hasDerivAt_scalarAt_const (t₀ : ℝ) (x : M) :
    HasDerivAt (fun _ : ℝ ↦ g.scalarAt x) 0 t₀ := by
  simpa using hasDerivAt_const t₀ (g.scalarAt x)

end StaticFlat

end ClosedSmoothRiemannianMetric

/--
Static Ricci-flat closed metrics satisfy the closed Hamilton scalar evolution
equation.

The Ricci-flatness hypothesis is the genuine pointwise bilinear vanishing
needed here: it implies both `scalarAt ≡ 0` and `ricciNormSqAt = 0`.
-/
theorem hamilton_scalar_evolution_static_flat
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (t₀ : ℝ) (x : M)
    (hric : ∀ y : M, ∀ u w : TM y, g.ricciAt y u w = 0) :
    SatisfiesHamiltonScalarEvolutionAt (fun _ : ℝ ↦ g) t₀ x := by
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (((fun _ : ℝ ↦ g) t).leviCivita) 1 :=
    fun _ ↦ inferInstance
  have hderiv : HasDerivAt (fun _ : ℝ ↦ g.scalarAt x) 0 t₀ :=
    g.hasDerivAt_scalarAt_const t₀ x
  have hlap : g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 :=
    g.laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero hric x
  have hnorm : g.ricciNormSqAt x = 0 :=
    g.ricciNormSqAt_eq_zero (hric x)
  have hrhs : g.laplacianAt (fun y ↦ g.scalarAt y) x + 2 * g.ricciNormSqAt x = 0 := by
    rw [hlap, hnorm]
    ring
  unfold SatisfiesHamiltonScalarEvolutionAt
  rw [hrhs]
  simpa using hderiv

/--
The unproven closed-manifold Hamilton scalar evolution frontier.

This definition is a target statement, not a theorem: every closed Ricci-flow
solution should satisfy `∂ₜ R = ΔR + 2 |Ric|²` once the required curvature
regularity for each time-slice is available.  The single-chart analogues are
`hamilton_scalar_evolution_of_bianchi`,
`hamilton_scalar_evolution_of_bianchi_curved`,
`hamilton_scalar_evolution_ricci_flow`,
`curved_ricci_flow_scalar_evolution`, and
`curved_ricci_flow_scalar_evolution_trace_form` in `ModelLaplacian.lean`.
-/
def HamiltonScalarEvolutionProgram : Prop :=
  ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
    IsClosedRicciFlowSolutionAt gt t₀ x →
      ∀ hcurv : ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
        letI : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
          hcurv
        SatisfiesHamiltonScalarEvolutionAt gt t₀ x

end Poincare
