import Poincare.Global.RicciFlow

/-!
# Metric time variation

This module introduces the pointwise time derivative of a closed smooth
Riemannian metric family.  It is only the vocabulary layer needed by the
closed scalar-evolution port: the metric-variation formula itself belongs to a
later file.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Pointwise differentiability in time of a metric family at a fixed base point.

This is a genuine differentiability hypothesis for every pair of tangent
vectors in the fiber over `x`; it carries no arbitrary proof certificate.
-/
def TimeDifferentiableAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ v w : TM x, DifferentiableAt ℝ (fun t ↦ (gt t).inner x v w) t₀

/-- The pointwise time derivative of a metric family at `(t₀, x)`. -/
def timeDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TM x → TM x → ℝ :=
  fun v w ↦ deriv (fun t ↦ (gt t).inner x v w) t₀

theorem TimeDifferentiableAt.inner
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) (v w : TM x) :
    DifferentiableAt ℝ (fun t ↦ (gt t).inner x v w) t₀ :=
  hgt v w

theorem timeDerivAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v w : TM x) :
    timeDerivAt gt t₀ x v w =
      deriv (fun t ↦ (gt t).inner x v w) t₀ :=
  rfl

/-- Symmetry of the metric time derivative, inherited from metric symmetry. -/
theorem timeDerivAt_symm
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v w : TM x) :
    timeDerivAt gt t₀ x v w = timeDerivAt gt t₀ x w v := by
  unfold timeDerivAt
  apply congrArg (fun f : ℝ → ℝ ↦ deriv f t₀)
  funext t
  exact (gt t).inner_symm x v w

/-- Additivity in the first tangent-vector argument. -/
theorem timeDerivAt_add_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) (v v' w : TM x) :
    timeDerivAt gt t₀ x (v + v') w =
      timeDerivAt gt t₀ x v w + timeDerivAt gt t₀ x v' w := by
  unfold timeDerivAt
  have hfun :
      (fun t ↦ (gt t).inner x (v + v') w) =
        fun t ↦ (gt t).inner x v w + (gt t).inner x v' w := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_add (hgt v w) (hgt v' w)

/-- Homogeneity in the first tangent-vector argument. -/
theorem timeDerivAt_smul_left
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) (c : ℝ) (v w : TM x) :
    timeDerivAt gt t₀ x (c • v) w = c • timeDerivAt gt t₀ x v w := by
  unfold timeDerivAt
  have hfun :
      (fun t ↦ (gt t).inner x (c • v) w) =
        fun t ↦ c • (gt t).inner x v w := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_const_smul c (hgt v w)

/-- Additivity in the second tangent-vector argument. -/
theorem timeDerivAt_add_right
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) (v w w' : TM x) :
    timeDerivAt gt t₀ x v (w + w') =
      timeDerivAt gt t₀ x v w + timeDerivAt gt t₀ x v w' := by
  unfold timeDerivAt
  have hfun :
      (fun t ↦ (gt t).inner x v (w + w')) =
        fun t ↦ (gt t).inner x v w + (gt t).inner x v w' := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_add (hgt v w) (hgt v w')

/-- Homogeneity in the second tangent-vector argument. -/
theorem timeDerivAt_smul_right
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) (c : ℝ) (v w : TM x) :
    timeDerivAt gt t₀ x v (c • w) = c • timeDerivAt gt t₀ x v w := by
  unfold timeDerivAt
  have hfun :
      (fun t ↦ (gt t).inner x v (c • w)) =
        fun t ↦ c • (gt t).inner x v w := by
    funext t
    simp
  rw [hfun]
  exact deriv_fun_const_smul c (hgt v w)

/-- The zero vector in the first slot gives zero time variation. -/
@[simp] theorem timeDerivAt_zero_left
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (w : TM x) :
    timeDerivAt gt t₀ x 0 w = 0 := by
  unfold timeDerivAt
  have hfun : (fun t ↦ (gt t).inner x 0 w) = fun _ : ℝ ↦ 0 := by
    funext t
    simp
  rw [hfun, deriv_const]

/-- The zero vector in the second slot gives zero time variation. -/
@[simp] theorem timeDerivAt_zero_right
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v : TM x) :
    timeDerivAt gt t₀ x v 0 = 0 := by
  unfold timeDerivAt
  have hfun : (fun t ↦ (gt t).inner x v 0) = fun _ : ℝ ↦ 0 := by
    funext t
    simp
  rw [hfun, deriv_const]

/--
The time derivative as an actual bilinear form once the metric family is
pointwise differentiable in time.
-/
noncomputable def timeDerivBilinAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hgt : TimeDifferentiableAt gt t₀ x) :
    LinearMap.BilinForm ℝ (TM x) :=
  LinearMap.mk₂ ℝ (timeDerivAt gt t₀ x)
    (fun v v' w ↦ timeDerivAt_add_left hgt v v' w)
    (fun c v w ↦ timeDerivAt_smul_left hgt c v w)
    (fun v w w' ↦ timeDerivAt_add_right hgt v w w')
    (fun c v w ↦ timeDerivAt_smul_right hgt c v w)

theorem timeDerivBilinAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hgt : TimeDifferentiableAt gt t₀ x) (v w : TM x) :
    timeDerivBilinAt gt t₀ x hgt v w = timeDerivAt gt t₀ x v w :=
  rfl

/-- Time-constant metric families are pointwise differentiable in time. -/
theorem timeDifferentiableAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    TimeDifferentiableAt (fun _ : ℝ ↦ g) t₀ x :=
  fun v w ↦ differentiableAt_const (c := g.inner x v w)

/-- Time-constant metric families have zero pointwise time derivative. -/
@[simp] theorem timeDerivAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (v w : TM x) :
    timeDerivAt (fun _ : ℝ ↦ g) t₀ x v w = 0 := by
  unfold timeDerivAt
  rw [deriv_const]

variable [T2Space M]

/--
Rephrase the closed Ricci-flow equation in terms of `timeDerivAt`.

This is only an unfolding theorem: it exposes the existing flow field of
`IsClosedRicciFlowSolutionAt` through the metric-variation vocabulary.
-/
theorem isClosedRicciFlowSolutionAt_timeDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    {Z : ∀ y : M, TM y} (hZ : ClosedC2TangentField Z)
    (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
    (w : TM x) :
    timeDerivAt gt t₀ x (Z x) w =
      -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w := by
  simpa [timeDerivAt, IsClosedRicciFlowSolutionAt] using
    hflow.flow hZ hreg w

end Poincare
