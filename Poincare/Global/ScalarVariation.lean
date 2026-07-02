import Poincare.Global.MetricVariation
import Poincare.Global.RicciNorm

/-!
# Scalar curvature variation: first closed-manifold layer

This file records the first reusable closed-manifold facts needed before the
full scalar-variation formula can be ported from the model-space chain in
`ModelLaplacian.lean`.

The main proved step is the finite-dimensional trace decomposition: once the
raised Ricci endomorphism has a genuine time derivative, scalar curvature has
a time derivative and its derivative is the trace of that Ricci-endomorphism
derivative.  This is the closed analogue of the model theorem
`RicciFlow.RicciFlow.hasDerivAt_trace`.

The later Lichnerowicz target is intentionally not encoded here as a fake
placeholder: the closed-manifold double-divergence vocabulary is still missing.
The intended shape is recorded in `harness/reports/M3-scalar-variation_notes.md`
against the model analogues `ricciDeriv_*`,
`lichnerowiczLaplacian_*`, `g_covDeltaGammaDeriv_lichnerowicz`, and
`hamilton_scalar_evolution_of_bianchi`.
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

namespace ClosedSmoothRiemannianMetric

/--
The raised Ricci endomorphism as a continuous-linear map on the tangent fiber.

The underlying geometric object is `g.ricciEndoAt x`; the wrapper lets us use
the existing trace derivative theorem for paths in `E →L[ℝ] E`.
-/
noncomputable def ricciEndoContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : TM x →L[ℝ] TM x :=
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (g.ricciEndoAt x)

theorem ricciEndoContinuousAt_coe
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    (g.ricciEndoContinuousAt x : TM x →ₗ[ℝ] TM x) = g.ricciEndoAt x := by
  rfl

/-- Scalar curvature is the trace of the continuous-linear Ricci endomorphism. -/
theorem scalarAt_eq_trace_ricciEndoContinuousAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    g.scalarAt x =
      LinearMap.trace ℝ (TM x) (g.ricciEndoContinuousAt x : TM x →ₗ[ℝ] TM x) := by
  rw [g.scalarAt_eq_trace_ricciEndoAt]
  rfl

/--
Honest time differentiability hypothesis for the raised Ricci endomorphism.

This is stronger than differentiability of each Ricci component: it asserts a
derivative of the actual endomorphism path on the finite-dimensional tangent
fiber.
-/
def RicciEndoHasDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (A' : TM x →L[ℝ] TM x) : Prop :=
  HasDerivAt (fun t ↦ (gt t).ricciEndoContinuousAt x) A' t₀

/--
The trace decomposition for scalar variation: differentiating the trace of the
raised Ricci endomorphism gives the trace of the endomorphism derivative.
-/
theorem hasDerivAt_trace_ricciEndoContinuousAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    HasDerivAt
      (fun t ↦ LinearMap.trace ℝ (TM x)
        ((gt t).ricciEndoContinuousAt x : TM x →ₗ[ℝ] TM x))
      (LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x)) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact RicciFlow.RicciFlow.hasDerivAt_trace hA

/--
Differentiability layer for scalar curvature from a genuine Ricci-endomorphism
time derivative.
-/
theorem hasDerivAt_scalarAt_of_ricciEndoHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    HasDerivAt (fun t ↦ (gt t).scalarAt x)
      (LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x)) t₀ := by
  have htrace := hasDerivAt_trace_ricciEndoContinuousAt hA
  convert htrace using 1

/-- The `DifferentiableAt` prerequisite for `SatisfiesHamiltonScalarEvolutionAt`. -/
theorem differentiableAt_scalarAt_of_ricciEndoHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    DifferentiableAt ℝ (fun t ↦ (gt t).scalarAt x) t₀ :=
  (hasDerivAt_scalarAt_of_ricciEndoHasDerivAt hA).differentiableAt

/-- Formula for `deriv scalarAt` once the Ricci-endomorphism derivative is known. -/
theorem deriv_scalarAt_eq_trace_of_ricciEndoHasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {A' : TM x →L[ℝ] TM x}
    (hA : RicciEndoHasDerivAt gt t₀ x A') :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      LinearMap.trace ℝ (TM x) (A' : TM x →ₗ[ℝ] TM x) :=
  (hasDerivAt_scalarAt_of_ricciEndoHasDerivAt hA).deriv

end ClosedSmoothRiemannianMetric

/--
Honest time differentiability hypothesis for canonical connection values on
canonical extended sections.

This is the closed-manifold analogue of the model `christoffelDeriv`
regularity input, but stated directly for the canonical Levi-Civita connection.
-/
def ConnectionValueTimeDifferentiableAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ v w : TM x, DifferentiableAt ℝ
    (fun t ↦ (gt t).leviCivita (extend E w) x v) t₀

/--
The pointwise connection variation `δΓ(v,w)`, defined as the time derivative
of the canonical Levi-Civita connection applied to the canonical extension of
`w` in direction `v`.
-/
noncomputable def deltaGammaAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TM x → TM x → TM x :=
  fun v w ↦
    letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
    deriv (fun t ↦ (gt t).leviCivita (extend E w) x v) t₀

theorem deltaGammaAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v w : TM x) :
    deltaGammaAt gt t₀ x v w =
      deriv (fun t ↦ (gt t).leviCivita (extend E w) x v) t₀ :=
  rfl

/-- If the connection-value path has derivative `Γ'`, `deltaGammaAt` recovers it. -/
theorem deltaGammaAt_eq_of_hasDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    {v w : TM x} {Γ' : TM x}
    (hΓ : HasDerivAt (fun t ↦ (gt t).leviCivita (extend E w) x v) Γ' t₀) :
    deltaGammaAt gt t₀ x v w = Γ' := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  exact hΓ.deriv

/-- Additivity of `δΓ` in its direction slot. -/
theorem deltaGammaAt_add_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (v v' w : TM x) :
    deltaGammaAt gt t₀ x (v + v') w =
      deltaGammaAt gt t₀ x v w + deltaGammaAt gt t₀ x v' w := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  have hfun :
      (fun t ↦ (gt t).leviCivita (extend E w) x (v + v')) =
        fun t ↦ (gt t).leviCivita (extend E w) x v +
          (gt t).leviCivita (extend E w) x v' := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_add (hΓ v w) (hΓ v' w)

/-- Homogeneity of `δΓ` in its direction slot. -/
theorem deltaGammaAt_smul_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    (c : ℝ) (v w : TM x) :
    deltaGammaAt gt t₀ x (c • v) w = c • deltaGammaAt gt t₀ x v w := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  have hfun :
      (fun t ↦ (gt t).leviCivita (extend E w) x (c • v)) =
        fun t ↦ c • (gt t).leviCivita (extend E w) x v := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_const_smul c (hΓ v w)

/-- Time-constant families have differentiable connection values. -/
theorem connectionValueTimeDifferentiableAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    ConnectionValueTimeDifferentiableAt (fun _ : ℝ ↦ g) t₀ x :=
  fun v w ↦ differentiableAt_const
    (c := g.leviCivita (extend E w) x v)

/-- The connection variation of a time-constant family vanishes. -/
@[simp] theorem deltaGammaAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v w : TM x) :
    deltaGammaAt (fun _ : ℝ ↦ g) t₀ x v w = 0 := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  unfold deltaGammaAt
  rw [deriv_const]

end Poincare
