import Poincare.Global.BumpExtend

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

/--
Regularity needed to test the Ricci-flow equation on canonical extensions of
arbitrary tangent vectors at `x`.

This is the honest bridge from the section-tested flow equation to the
pointwise bilinear variation tensor.  The canonical extensions only need local
`DerivRegularAt`; the globally admissible test field is supplied by
`bumpExtend`, which agrees with the canonical extension near the anchor.
-/
def ClosedRicciFlowExtensionRegularAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  ∀ v : TM x,
    CovariantDerivative.DerivRegularAt (gt t₀).leviCivita (extend E v) x

/--
Canonical tangent extensions are locally regular for every smooth metric
slice.  Consequently extension regularity is automatic for an arbitrary
closed smooth metric family; it is not additional Ricci-flow data.
-/
theorem closedRicciFlowExtensionRegularAt_canonical
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    ClosedRicciFlowExtensionRegularAt gt t₀ x := by
  intro v
  exact CovariantDerivative.derivRegularAt_extend
    (cov := (gt t₀).leviCivita) (x := x) v

/-- A global closed Ricci-flow equation supplies the former flow-plus-extension
package because the extension component is canonical. -/
theorem global_isClosedRicciFlowSolutionAt_and_extensionRegularAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (hFlow : ∀ x : M, IsClosedRicciFlowSolutionAt gt t₀ x) :
    ∀ x : M,
      IsClosedRicciFlowSolutionAt gt t₀ x ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ x :=
  fun x ↦ ⟨hFlow x,
    closedRicciFlowExtensionRegularAt_canonical gt t₀ x⟩

/--
Legacy constructor: global `C²` canonical extensions still imply the local
extension-regularity bundle.
-/
theorem closedRicciFlowExtensionRegularAt_const_of_closedC2_extend
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hExtend : ∀ v : TM x, ClosedC2TangentField (extend E v)) :
    ClosedRicciFlowExtensionRegularAt (fun _ : ℝ ↦ g) t₀ x := by
  intro v
  exact CovariantDerivative.derivRegularAt_of_contMDiff
    (cov := g.leviCivita) (hExtend v) x

/--
Time-constant metric families satisfy the local extension-regularity bundle.

This is the non-vacuous static witness unlocked by the bump globalization:
canonical extensions are only required to be locally regular at the anchor.
-/
theorem closedRicciFlowExtensionRegularAt_const
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    ClosedRicciFlowExtensionRegularAt (fun _ : ℝ ↦ g) t₀ x := by
  intro v
  exact CovariantDerivative.derivRegularAt_extend
    (cov := g.leviCivita) (x := x) v

/--
Static Ricci-flat closed metric families supply the neighborhood flow-plus-
extension package consumed by the scalar-evolution chain.
-/
theorem eventually_isClosedRicciFlowSolutionAt_const_and_extensionRegularAt_of_ricciFlat
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hric : ∀ y : M, ∀ {Z : ∀ z : M, TM z}, ClosedC2TangentField Z →
      ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z y) (w : TM y),
        CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0) :
    ∀ᶠ y in nhds x,
      IsClosedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t₀ y ∧
        ClosedRicciFlowExtensionRegularAt (fun _ : ℝ ↦ g) t₀ y :=
  Filter.Eventually.of_forall fun y ↦
    ⟨isClosedRicciFlowSolutionAt_const_of_ricciFlat
      (g := g) (x := y) (hric y) t₀,
     closedRicciFlowExtensionRegularAt_const (g := g) t₀ y⟩

/--
Under the closed Ricci-flow equation, the metric time derivative is
pointwise `-2 Ric` on tangent vectors once canonical extensions are admissible.
-/
theorem isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (v w : TM x) :
    timeDerivAt gt t₀ x v w = -2 * (gt t₀).ricciAt x v w := by
  let Z : ∀ y : M, TM y := bumpExtend (n := n) (M := M) x v
  have hZ : ClosedC2TangentField Z := by
    simpa [Z] using bumpExtend_closedC2TangentField (n := n) (M := M) x v
  have hregZ : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x := by
    exact CovariantDerivative.derivRegularAt_of_contMDiff
      (cov := (gt t₀).leviCivita) hZ x
  have hregExt :
      CovariantDerivative.DerivRegularAt (gt t₀).leviCivita (extend E v) x :=
    hext v
  have hflow' :=
    isClosedRicciFlowSolutionAt_timeDerivAt
      (gt := gt) (t₀ := t₀) (x := x) hflow
      (Z := Z) hZ hregZ w
  have htraceCongr :
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregZ w =
        CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w := by
    exact ricciTraceAt_congr_of_eventuallyEq
      (cov := (gt t₀).leviCivita)
      (Z := Z) (Z' := extend E v) (x := x)
      (by simpa [Z] using (hZ x))
      (FiberBundle.contMDiffAt_extend' (k := 2) I E v)
      hregZ hregExt
      (by simpa [Z] using
        (bumpExtend_eventuallyEq_extend (n := n) (M := M) x v))
      w
  have htrace :
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w =
        (gt t₀).ricciAt x v w := by
    have h :=
      CovariantDerivative.ricciTraceAt_eq_ricciBilinearAt
        (cov := (gt t₀).leviCivita) (Z := extend E v) (x := x)
        (FiberBundle.contMDiffAt_extend' (k := 2) I E v) hregExt w
    calc
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w =
          (gt t₀).ricciAt x w v := by
            simpa [ClosedSmoothRiemannianMetric.ricciAt] using h
      _ = (gt t₀).ricciAt x v w := (gt t₀).ricciAt_symm x w v
  rw [htraceCongr, htrace] at hflow'
  simpa [Z] using hflow'

end Poincare
