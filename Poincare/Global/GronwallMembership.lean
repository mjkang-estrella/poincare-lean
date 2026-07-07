import Poincare.Global.SpeedGeneric

/-!
# A-priori Gronwall membership for Jacobi norm triples

This module records the non-pinned membership route for the Jacobi norm system.
The core estimate is purely a-priori: a curve solving a linear ODE
`x' = A(t) x`, with `‖A(t)‖ ≤ C` on `[0,T]`, stays in the zero-centered ball
of radius `‖x(0)‖ * exp (C*T)`.  Translating the estimate to a ball centered at
the initial state gives the closed-ball shape used by the scalar PL packages,
without invoking any pinned-value theorem.

The final section connects the actual corrected Jacobi norm triple to the
speed-generic norm ODE.  That bridge uses the pointwise curvature/linearized
state feed from `SpeedGeneric`, not the pinned uniqueness theorem.
-/

noncomputable section

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GronwallMembership

local notation "Triple" => ℝ × ℝ × ℝ

section LinearODE

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
A-priori Gronwall bound for a linear ODE on `[0,T]`.

This is the non-circular estimate: it uses only the differential equation and a
uniform operator-norm bound, not any identification with a pinned solution.
-/
theorem linearODE_norm_le_exp_of_opNorm_le
    {A : ℝ → X →L[ℝ] X} {x : ℝ → X} {C T t : ℝ}
    (hxcont : ContinuousOn x (Icc (0 : ℝ) T))
    (hxderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt x (A τ (x τ)) (Ici τ) τ)
    (hAop : ∀ τ ∈ Ico (0 : ℝ) T, ‖A τ‖ ≤ C)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖x t‖ ≤ ‖x 0‖ * Real.exp (C * t) := by
  have hbound : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖A τ (x τ)‖ ≤ C * ‖x τ‖ + 0 := by
    intro τ hτ
    calc
      ‖A τ (x τ)‖ ≤ ‖A τ‖ * ‖x τ‖ :=
        ContinuousLinearMap.le_opNorm (A τ) (x τ)
      _ ≤ C * ‖x τ‖ := by
        exact mul_le_mul_of_nonneg_right (hAop τ hτ) (norm_nonneg _)
      _ = C * ‖x τ‖ + 0 := by ring
  have hgr :
      ‖x t‖ ≤ gronwallBound ‖x 0‖ C 0 (t - 0) :=
    norm_le_gronwallBound_of_norm_deriv_right_le
      (f := x) (f' := fun τ => A τ (x τ))
      (δ := ‖x 0‖) (K := C) (ε := 0)
      (a := 0) (b := T) hxcont hxderiv (by rfl) hbound t ht
  simpa [sub_zero, gronwallBound_ε0] using hgr

/-- Uniform endpoint version of `linearODE_norm_le_exp_of_opNorm_le`. -/
theorem linearODE_norm_le_exp_T_of_opNorm_le
    {A : ℝ → X →L[ℝ] X} {x : ℝ → X} {C T t : ℝ}
    (hC : 0 ≤ C)
    (hxcont : ContinuousOn x (Icc (0 : ℝ) T))
    (hxderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt x (A τ (x τ)) (Ici τ) τ)
    (hAop : ∀ τ ∈ Ico (0 : ℝ) T, ‖A τ‖ ≤ C)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖x t‖ ≤ ‖x 0‖ * Real.exp (C * T) := by
  have hpoint :=
    linearODE_norm_le_exp_of_opNorm_le
      (A := A) (x := x) (C := C) hxcont hxderiv hAop ht
  have hexp : Real.exp (C * t) ≤ Real.exp (C * T) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hC)
  exact hpoint.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg _))

/-- Zero-centered closed-ball membership from the a-priori Gronwall bound. -/
theorem linearODE_mem_closedBall_zero_of_opNorm_le
    {A : ℝ → X →L[ℝ] X} {x : ℝ → X} {C T t : ℝ}
    (hC : 0 ≤ C)
    (hxcont : ContinuousOn x (Icc (0 : ℝ) T))
    (hxderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt x (A τ (x τ)) (Ici τ) τ)
    (hAop : ∀ τ ∈ Ico (0 : ℝ) T, ‖A τ‖ ≤ C)
    (ht : t ∈ Icc (0 : ℝ) T) :
    x t ∈ closedBall (0 : X) (‖x 0‖ * Real.exp (C * T)) := by
  rw [mem_closedBall, dist_eq_norm]
  simpa using
    linearODE_norm_le_exp_T_of_opNorm_le
      (A := A) (x := x) (C := C) hC hxcont hxderiv hAop ht

/--
Closed-ball membership centered at the initial state.  The radius is deliberately
generous; it is enough for PL membership and follows from the zero-centered
Gronwall estimate by the triangle inequality.
-/
theorem linearODE_mem_closedBall_initial_of_opNorm_le
    {A : ℝ → X →L[ℝ] X} {x : ℝ → X} {C T t : ℝ}
    (hC : 0 ≤ C)
    (hxcont : ContinuousOn x (Icc (0 : ℝ) T))
    (hxderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt x (A τ (x τ)) (Ici τ) τ)
    (hAop : ∀ τ ∈ Ico (0 : ℝ) T, ‖A τ‖ ≤ C)
    (ht : t ∈ Icc (0 : ℝ) T) :
    x t ∈ closedBall (x 0) (‖x 0‖ * Real.exp (C * T) + ‖x 0‖) := by
  rw [mem_closedBall, dist_eq_norm]
  have hzero :=
    linearODE_norm_le_exp_T_of_opNorm_le
      (A := A) (x := x) (C := C) hC hxcont hxderiv hAop ht
  calc
    ‖x t - x 0‖ ≤ ‖x t‖ + ‖x 0‖ := norm_sub_le (x t) (x 0)
    _ ≤ ‖x 0‖ * Real.exp (C * T) + ‖x 0‖ := by
      exact add_le_add hzero le_rfl

/-- Fixed-radius version of `linearODE_mem_closedBall_initial_of_opNorm_le`. -/
theorem linearODE_mem_closedBall_initial_of_radius_ge
    {A : ℝ → X →L[ℝ] X} {x : ℝ → X} {C T t : ℝ} {radius : ℝ≥0}
    (hC : 0 ≤ C)
    (hxcont : ContinuousOn x (Icc (0 : ℝ) T))
    (hxderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt x (A τ (x τ)) (Ici τ) τ)
    (hAop : ∀ τ ∈ Ico (0 : ℝ) T, ‖A τ‖ ≤ C)
    (hradius : ‖x 0‖ * Real.exp (C * T) + ‖x 0‖ ≤ (radius : ℝ))
    (ht : t ∈ Icc (0 : ℝ) T) :
    x t ∈ closedBall (x 0) (radius : ℝ) := by
  have hmem :=
    linearODE_mem_closedBall_initial_of_opNorm_le
      (A := A) (x := x) (C := C) hC hxcont hxderiv hAop ht
  rw [mem_closedBall] at hmem ⊢
  exact hmem.trans hradius

end LinearODE

section NormState

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/-- Corrected covariant derivative component used by the norm scalars. -/
def correctedD
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (γ Ψ : ℝ → E3 × E3) (t : ℝ) : E3 :=
  (Ψ t).2 + (chartChristoffelField g x₀ (γ t).1) (γ t).2 (Ψ t).1

/-- The actual corrected Jacobi norm triple. -/
def normState
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (γ Ψ : ℝ → E3 × E3) (t : ℝ) : Triple :=
  (JacobiNormSystem.normA g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ τ).1) t,
    JacobiNormSystem.normB g x₀
      (fun τ : ℝ => (γ τ).1)
      (fun τ : ℝ => (Ψ τ).1)
      (correctedD g x₀ γ Ψ) t,
    JacobiNormSystem.normC g x₀
      (fun τ : ℝ => (γ τ).1)
      (correctedD g x₀ γ Ψ) t)

/--
The actual corrected norm triple satisfies the speed-generic linear norm ODE at
one time.  This is the non-pinned bridge used by the Gronwall membership layer.
-/
theorem normState_hasDerivAt_speed
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {t speed : ℝ}
    (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : HasDerivAt γ
      (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hΨ : HasDerivAt Ψ
      (linearizedGeodesicFlowFieldAlong
        (chartChristoffelField g x₀) γ t (Ψ t)) t)
    (htarget : (γ t).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 (γ t).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed :
      CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 =
        speed ^ 2)
    (horth : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (Ψ t).1 (γ t).2 = 0)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ t).1) :
    HasDerivAt (normState g x₀ γ Ψ) (Aop (normState g x₀ γ Ψ t)) t := by
  have hfeed :=
    JacobiNormClose.chart_linearized_state_feeds_speed_norm_system_at
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := t)
      (speed := speed) hγ hΨ htarget hχone hspeed horth hGd
  have hprod := hfeed.1.prodMk (hfeed.2.1.prodMk hfeed.2.2)
  simpa [normState, correctedD, hAop] using hprod

/-- Interval form of `normState_hasDerivAt_speed`. -/
theorem normState_hasDerivWithinAt_speed_on_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {T speed : ℝ}
    (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        speed ^ 2)
    (horth : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1) :
    ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (normState g x₀ γ Ψ)
        (Aop (normState g x₀ γ Ψ s)) (Icc (0 : ℝ) T) s := by
  intro s hs
  exact
    (normState_hasDerivAt_speed
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
      (speed := speed) Aop hAop
      (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
      (hspeed s hs) (horth s hs) (hGd s hs)).hasDerivWithinAt

/-- Continuity of the norm-state curve on `[0,T]`, derived from the ODE bridge. -/
theorem normState_continuousOn_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {T speed : ℝ}
    (Aop : Triple →L[ℝ] Triple)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        speed ^ 2)
    (horth : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1) :
    ContinuousOn (normState g x₀ γ Ψ) (Icc (0 : ℝ) T) := by
  refine HasDerivWithinAt.continuousOn
    (f' := fun s : ℝ => Aop (normState g x₀ γ Ψ s)) ?_
  exact normState_hasDerivWithinAt_speed_on_Icc
    (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
    (T := T) (speed := speed) Aop hAop
    hγ hΨ htarget hχone hspeed horth hGd

/--
Zero-centered a-priori Gronwall membership for the actual corrected norm triple.
-/
theorem normState_mem_closedBall_zero_of_opNorm_le
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {T speed C : ℝ}
    (Aop : Triple →L[ℝ] Triple)
    (hAopShape : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hγ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        speed ^ 2)
    (horth : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1) :
    ∀ s ∈ Icc (0 : ℝ) T,
      normState g x₀ γ Ψ s ∈
        closedBall (0 : Triple)
          (‖normState g x₀ γ Ψ 0‖ * Real.exp (C * T)) := by
  intro s hs
  have hcont :
      ContinuousOn (normState g x₀ γ Ψ) (Icc (0 : ℝ) T) :=
    normState_continuousOn_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (T := T) (speed := speed) Aop hAopShape
      hγ hΨ htarget hχone hspeed horth hGd
  have hderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (normState g x₀ γ Ψ)
        ((fun _ : ℝ => Aop) τ (normState g x₀ γ Ψ τ)) (Ici τ) τ := by
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self hτ
    simpa using
      (normState_hasDerivAt_speed
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := τ)
        (speed := speed) Aop hAopShape
        (hγ τ hτIcc) (hΨ τ hτIcc) (htarget τ hτIcc)
        (hχone τ hτIcc) (hspeed τ hτIcc) (horth τ hτIcc)
        (hGd τ hτIcc)).hasDerivWithinAt
  exact
    linearODE_mem_closedBall_zero_of_opNorm_le
      (A := fun _ : ℝ => Aop) (x := normState g x₀ γ Ψ)
      (C := C) hC hcont hderiv (fun _ _ => hAopNorm) hs

/--
Initial-state centered a-priori Gronwall membership for the actual corrected
norm triple.
-/
theorem normState_mem_closedBall_initial_of_opNorm_le
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {T speed C : ℝ}
    (Aop : Triple →L[ℝ] Triple)
    (hAopShape : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hγ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        speed ^ 2)
    (horth : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1) :
    ∀ s ∈ Icc (0 : ℝ) T,
      normState g x₀ γ Ψ s ∈
        closedBall (normState g x₀ γ Ψ 0)
          (‖normState g x₀ γ Ψ 0‖ * Real.exp (C * T) +
            ‖normState g x₀ γ Ψ 0‖) := by
  intro s hs
  have hcont :
      ContinuousOn (normState g x₀ γ Ψ) (Icc (0 : ℝ) T) :=
    normState_continuousOn_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (T := T) (speed := speed) Aop hAopShape
      hγ hΨ htarget hχone hspeed horth hGd
  have hderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (normState g x₀ γ Ψ)
        ((fun _ : ℝ => Aop) τ (normState g x₀ γ Ψ τ)) (Ici τ) τ := by
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self hτ
    simpa using
      (normState_hasDerivAt_speed
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := τ)
        (speed := speed) Aop hAopShape
        (hγ τ hτIcc) (hΨ τ hτIcc) (htarget τ hτIcc)
        (hχone τ hτIcc) (hspeed τ hτIcc) (horth τ hτIcc)
        (hGd τ hτIcc)).hasDerivWithinAt
  exact
    linearODE_mem_closedBall_initial_of_opNorm_le
      (A := fun _ : ℝ => Aop) (x := normState g x₀ γ Ψ)
      (C := C) hC hcont hderiv (fun _ _ => hAopNorm) hs

theorem norm_triple_zero_zero (q : ℝ) :
    ‖(((0 : ℝ), (0 : ℝ), q) : Triple)‖ = |q| := by
  simp [Prod.norm_mk, Real.norm_eq_abs]

/-- If the initial quadratic value is bounded by `qmax`, so is its Gronwall radius. -/
theorem qcenter_gronwall_radius_le_of_abs_le {q qmax C T : ℝ}
    (hq : |q| ≤ qmax) :
    |q| * Real.exp (C * T) + |q| ≤
      qmax * Real.exp (C * T) + qmax := by
  exact add_le_add
    (mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le) hq

/--
The `SolutionsFeed`-shaped center version after substituting the genuine
initial values `(0,0,q)`.
-/
theorem normState_mem_closedBall_qcenter_of_opNorm_le
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {T speed C q : ℝ}
    (Aop : Triple →L[ℝ] Triple)
    (hAopShape : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hγ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        speed ^ 2)
    (horth : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (ha0 :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (correctedD g x₀ γ Ψ) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (correctedD g x₀ γ Ψ) 0 = q) :
    ∀ s ∈ Icc (0 : ℝ) T,
      normState g x₀ γ Ψ s ∈
        closedBall (((0 : ℝ), (0 : ℝ), q) : Triple)
          (|q| * Real.exp (C * T) + |q|) := by
  have hinit :
      normState g x₀ γ Ψ 0 = (((0 : ℝ), (0 : ℝ), q) : Triple) := by
    simp [normState, ha0, hb0, hc0]
  intro s hs
  have hmem :=
    normState_mem_closedBall_initial_of_opNorm_le
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (T := T) (speed := speed) (C := C) Aop hAopShape hC hAopNorm
      hγ hΨ htarget hχone hspeed horth hGd s hs
  simpa [hinit, norm_triple_zero_zero] using hmem

/--
Fixed-radius version of the `q`-centered a-priori membership.  This is the
form that can feed a bounded-`w` package once a single `q_max` bound has been
extracted on the chosen `w`-ball.
-/
theorem normState_mem_closedBall_qcenter_of_radius_ge
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {T speed C q : ℝ}
    (Aop : Triple →L[ℝ] Triple)
    (hAopShape : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    {radius : ℝ≥0}
    (hradius : |q| * Real.exp (C * T) + |q| ≤ (radius : ℝ))
    (hγ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        speed ^ 2)
    (horth : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (ha0 :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (correctedD g x₀ γ Ψ) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (correctedD g x₀ γ Ψ) 0 = q) :
    ∀ s ∈ Icc (0 : ℝ) T,
      normState g x₀ γ Ψ s ∈
        closedBall (((0 : ℝ), (0 : ℝ), q) : Triple) (radius : ℝ) := by
  intro s hs
  have hmem :=
    normState_mem_closedBall_qcenter_of_opNorm_le
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (T := T) (speed := speed) (C := C) (q := q)
      Aop hAopShape hC hAopNorm
      hγ hΨ htarget hχone hspeed horth hGd ha0 hb0 hc0 s hs
  rw [mem_closedBall] at hmem ⊢
  exact hmem.trans hradius

end NormState

end GronwallMembership
end Poincare
