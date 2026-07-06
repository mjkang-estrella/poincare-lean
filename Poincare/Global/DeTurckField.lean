import Poincare.Global.DeTurck

/-!
# DeTurck vector field

This module constructs the pointwise DeTurck vector field from a metric `g`
and a fixed background metric `bg`, staying inside the genuine `Global/`
vocabulary.  The field is the `g`-trace of the connection difference
`Γ(g) - Γ(bg)` in the canonical `extend` frame:

`W = Σᵢ (∇ᵍ_{bᵢ} bⁱ - ∇ᵇᵍ_{bᵢ} bⁱ)`,

where `b` is the finite tangent basis at the base point and `bⁱ` is the
`g`-metric-dual vector to the coordinate covector `b.coord i`.  In coordinates
this is `W^k = g^{ij} (Γ(g)^k_{ij} - Γ(bg)^k_{ij})`.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

section General

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Pointwise connection difference in the canonical `extend` frame.

The value at tangent inputs `u w : TM x` is
`(∇ᵍ_u extend(w)) x - (∇ᵇᵍ_u extend(w)) x`, written in Mathlib's convention as
`(g.leviCivita (extend E w) x) u - (bg.leviCivita (extend E w) x) u`.
-/
noncomputable def deTurckConnectionDifferenceAt
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) (u w : TM x) : TM x :=
  (g.leviCivita (extend E w) x) u -
    (bg.leviCivita (extend E w) x) u

/-- The connection difference of a metric with itself vanishes pointwise. -/
@[simp] theorem deTurckConnectionDifferenceAt_self
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (u w : TM x) :
    deTurckConnectionDifferenceAt g g x u w = 0 := by
  simp [deTurckConnectionDifferenceAt]

/--
The DeTurck vector field at a point: the `g`-trace of
`Γ(g) - Γ(bg)` in the canonical extension frame.
-/
noncomputable def deTurckVectorFieldAt
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) : TM x :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ∑ i, deTurckConnectionDifferenceAt g bg x
    ((Module.finBasis ℝ (TM x)) i)
    (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))

/-- The DeTurck vector field of a metric against itself is zero. -/
@[simp] theorem deTurckVectorFieldAt_self
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    deTurckVectorFieldAt g g x = 0 := by
  simp [deTurckVectorFieldAt]

/-- The DeTurck vector field associated to a time-dependent metric family. -/
noncomputable def deTurckVectorField
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) : ∀ x : M, TM x :=
  fun x ↦ deTurckVectorFieldAt (gt t) bg x

@[simp] theorem deTurckVectorField_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) (x : M) :
    deTurckVectorField gt bg t x = deTurckVectorFieldAt (gt t) bg x :=
  rfl

/--
Regularity obligation for the constructed DeTurck vector field at one time.

This is an honest proposition, not an instance: proving it from metric
smoothness is a later analytic task.
-/
def DeTurckVectorFieldRegularAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) : Prop :=
  ClosedC2TangentField (n := n) (M := M) (deTurckVectorField gt bg t)

/--
Ricci-DeTurck flow specialized to the concrete DeTurck vector field built from
`gt` and the fixed background metric `bg`.
-/
def IsDeTurckGaugedFlowAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  IsClosedRicciDeTurckSolutionAt gt (fun t ↦ deTurckVectorField gt bg t) t₀ x

/-- Definitional unfolding of the concrete gauged-flow predicate. -/
theorem isDeTurckGaugedFlowAt_iff
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    IsDeTurckGaugedFlowAt gt bg t₀ x ↔
      IsClosedRicciDeTurckSolutionAt gt
        (fun t ↦ deTurckVectorField gt bg t) t₀ x :=
  Iff.rfl

/--
For a constant family gauged against the same metric, the concrete
Ricci-DeTurck predicate is definitionally the zero-field case and therefore
reduces to the closed Ricci-flow predicate.
-/
theorem isDeTurckGaugedFlowAt_const_self_iff_isClosedRicciFlowSolutionAt
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    IsDeTurckGaugedFlowAt (fun _ : ℝ ↦ g) g t₀ x ↔
      IsClosedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t₀ x := by
  have hWzero :
      (fun t ↦ deTurckVectorField (fun _ : ℝ ↦ g) g t) t₀ = 0 := by
    funext y
    simp [deTurckVectorField]
  simpa [IsDeTurckGaugedFlowAt] using
    (isClosedRicciDeTurckSolutionAt_iff_isClosedRicciFlowSolutionAt_of_zero
      (gt := fun _ : ℝ ↦ g)
      (Wt := fun t ↦ deTurckVectorField (fun _ : ℝ ↦ g) g t)
      (t₀ := t₀) (x := x) hWzero)

end General

section DimensionThree

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

/--
Static Ricci-flat metrics satisfy the concrete DeTurck-gauged flow predicate
when the background metric is the same static metric.
-/
theorem static_ricciFlat_deTurckGaugedFlowClause
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hric : ∀ x : M, ∀ {Z : ∀ y : M, TM3 y},
      ClosedC2TangentField (n := 3) (M := M) Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x)
          (w : TM3 x),
          CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0)
    (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsDeTurckGaugedFlowAt (fun _ : ℝ ↦ g) g t x := by
  have hflow := static_ricciFlat_flowClause (M := M) (g := g) hric T
  intro t ht x
  exact
    (isDeTurckGaugedFlowAt_const_self_iff_isClosedRicciFlowSolutionAt
      (n := 3) (M := M) (g := g) (t₀ := t) (x := x)).2
      (hflow t ht x)

end DimensionThree

end Poincare
