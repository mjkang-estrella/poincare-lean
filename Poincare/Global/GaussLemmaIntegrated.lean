import Poincare.Global.GaussLemmaTransverse
import Poincare.Global.GeodesicFlowDerivative

/-!
# Integrated transverse chart Gauss lemma

This module packages the three local ingredients for the transverse chart
Gauss lemma:

* the fixed-time initial-velocity derivative of the geodesic flow;
* the pointwise transverse Gauss identity;
* constant speed for each member of the radial initial-velocity family.

For the radial family `s ↦ α (z₀, v + s • w)`, the Jacobi initial state is
`Ψ 0 = (0, w)`.  Consequently the integrated pairing has zero constant term:

`G(γ t)(J t, γ' t) = t * G(z₀)(v, w)`.

The orthogonal case `G(z₀)(v, w) = 0` is the chart-form transverse Gauss
lemma on the common interval.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/--
Projecting the chart linearized geodesic system to its first component gives
`J' = K`.  This is the component of the linearized system consumed by the
transverse pairing identity.
-/
theorem chart_linearizedGeodesicFlowFieldAlong_fst
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (γ : ℝ → E × E) (t : ℝ) (ψ : E × E) :
    (linearizedGeodesicFlowFieldAlong (chartChristoffelField g x₀) γ t ψ).1 =
      ψ.2 := by
  let F : E × E → E × E := geodesicFlowField (chartChristoffelField g x₀)
  have hFdiff : DifferentiableAt ℝ F (γ t) :=
    (geodesicFlowField_chartChristoffelField_contDiff
      (g := g) (x₀ := x₀)).differentiable (by norm_num) (γ t)
  have hfst_apply :=
    congrArg (fun L : E × E →L[ℝ] E => L ψ) (fderiv.fst hFdiff)
  have hcoord :
      fderiv ℝ (fun p : E × E => (F p).1) (γ t) ψ = ψ.2 := by
    change (fderiv ℝ (fun p : E × E => p.2) (γ t)) ψ = ψ.2
    rw [fderiv_snd]
    rfl
  change ((fderiv ℝ F (γ t)) ψ).1 = ψ.2
  simpa [linearizedGeodesicFlowFieldAlong, linearizedGeodesicFlowOperator, F] using
    hfst_apply.symm.trans hcoord

omit [T2Space M] in
/-- The first component of a chart linearized solution has derivative equal to the second. -/
theorem chart_linearized_fst_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {γ Ψ : ℝ → E × E} {t : ℝ}
    (hΨ : HasDerivAt Ψ
      (linearizedGeodesicFlowFieldAlong
        (chartChristoffelField g x₀) γ t (Ψ t)) t) :
    HasDerivAt (fun τ : ℝ => (Ψ τ).1) (Ψ t).2 t := by
  have hfst := hΨ.hasFDerivAt.fst.hasDerivAt
  simpa [chart_linearizedGeodesicFlowFieldAlong_fst (g := g) (x₀ := x₀)
    (γ := γ) (t := t) (ψ := Ψ t)] using hfst

omit [T2Space M] in
/--
Fixed-time `s`-derivative of the speed scalar in the initial-velocity family.
The flow derivative supplies the two component derivatives of
`s ↦ α (z₀, v + s • w) t`.
-/
theorem chart_initialVelocity_speed_hasDerivAt_of_flowDerivative
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E} {t : ℝ}
    (hflow : HasDerivAt
      (fun s : ℝ => α (z₀, v + s • w) t) (Ψ t) 0)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀)
      (α (z₀, v) t).1) :
    HasDerivAt
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + s • w) t).1
          (α (z₀, v + s • w) t).2
          (α (z₀, v + s • w) t).2)
      (((fderiv ℝ (chartGeodesicMetric g x₀) (α (z₀, v) t).1)
          (Ψ t).1)
          (α (z₀, v) t).2 (α (z₀, v) t).2 +
        chartGeodesicMetric g x₀ (α (z₀, v) t).1
          (Ψ t).2 (α (z₀, v) t).2 +
        chartGeodesicMetric g x₀ (α (z₀, v) t).1
          (α (z₀, v) t).2 (Ψ t).2) 0 := by
  have hs_pos :
      HasDerivAt
        (fun s : ℝ => (α (z₀, v + s • w) t).1) (Ψ t).1 0 := by
    simpa using hflow.hasFDerivAt.fst.hasDerivAt
  have hs_vel :
      HasDerivAt
        (fun s : ℝ => (α (z₀, v + s • w) t).2) (Ψ t).2 0 := by
    simpa using hflow.hasFDerivAt.snd.hasDerivAt
  simpa using
    chart_geodesic_variation_speed_hasDerivAt
      (g := g) (x₀ := x₀)
      (z := fun s : ℝ => (α (z₀, v + s • w) t).1)
      (v := fun s : ℝ => (α (z₀, v + s • w) t).2)
      (s := 0) (J := (Ψ t).1) (K := (Ψ t).2)
      hs_pos hs_vel (by simpa using hGd)

omit [T2Space M] in
/--
The preceding speed derivative specialized to the uniform chart flow derivative
proved in `GeodesicFlowDerivative`.
-/
theorem chart_initialVelocity_speed_hasDerivAt_of_uniform_geodesicFlow
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {δ ε : ℝ} {a : ℝ≥0} {α : E × E → ℝ → E × E}
    {v w : E} {Ψ : ℝ → E × E} {t : ℝ}
    (hε : 0 < ε) (hv : ‖v‖ < δ)
    (hα : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ τ ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) τ))
            (Icc (-ε) ε) τ) ∧
        ∀ τ ∈ Icc (-ε) ε,
          α (extChartAt I x₀ x₀, v₀) τ ∈
            closedBall (extChartAt I x₀ x₀, (0 : E)) a)
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (hΨder : ∀ τ ∈ Icc (-ε) ε,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) τ (Ψ τ))
        (Icc (-ε) ε) τ)
    (ht : t ∈ Icc (0 : ℝ) ε)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀)
      (α (extChartAt I x₀ x₀, v) t).1) :
    HasDerivAt
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (extChartAt I x₀ x₀, v + s • w) t).1
          (α (extChartAt I x₀ x₀, v + s • w) t).2
          (α (extChartAt I x₀ x₀, v + s • w) t).2)
      (((fderiv ℝ (chartGeodesicMetric g x₀)
          (α (extChartAt I x₀ x₀, v) t).1) (Ψ t).1)
          (α (extChartAt I x₀ x₀, v) t).2
          (α (extChartAt I x₀ x₀, v) t).2 +
        chartGeodesicMetric g x₀ (α (extChartAt I x₀ x₀, v) t).1
          (Ψ t).2 (α (extChartAt I x₀ x₀, v) t).2 +
        chartGeodesicMetric g x₀ (α (extChartAt I x₀ x₀, v) t).1
          (α (extChartAt I x₀ x₀, v) t).2 (Ψ t).2) 0 := by
  exact
    chart_initialVelocity_speed_hasDerivAt_of_flowDerivative
      (g := g) (x₀ := x₀) (α := α)
      (z₀ := extChartAt I x₀ x₀) (v := v) (w := w) (Ψ := Ψ)
      (t := t)
      (chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := a)
        (α := α) (v := v) (w := w) (Ψ := Ψ)
        hε hv hα hΨ0 hΨder ht)
      hGd

omit [T2Space M] in
/-- Initial-speed derivative for `s ↦ G(z₀)(v + s • w, v + s • w)`. -/
theorem chart_initialVelocity_initialSpeed_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z₀ v w : E}
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀) :
    HasDerivAt
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + s • w) (v + s • w))
      (chartGeodesicMetric g x₀ z₀ w v +
        chartGeodesicMetric g x₀ z₀ v w) 0 := by
  have hz : HasDerivAt (fun _ : ℝ => z₀) (0 : E) 0 :=
    hasDerivAt_const (0 : ℝ) z₀
  have hv : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  simpa using
    chart_geodesic_variation_speed_hasDerivAt
      (g := g) (x₀ := x₀)
      (z := fun _ : ℝ => z₀)
      (v := fun s : ℝ => v + s • w)
      (s := 0) (J := (0 : E)) (K := w) hz hv hGd

omit [T2Space M] in
/--
Constant speed turns the fixed-time radial-family speed into the initial speed
as an eventual equality in the variation parameter.
-/
theorem chart_initialVelocity_speed_eventuallyEq_initialSpeed_of_constantSpeed
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {δ ε : ℝ} {α : E × E → ℝ → E × E} {z₀ v w : E} {t : ℝ}
    (hε : 0 < ε) (hv : ‖v‖ < δ)
    (hinit : ∀ v₀ : E, ‖v₀‖ < δ → α (z₀, v₀) 0 = (z₀, v₀))
    (hode : ∀ v₀ : E, ‖v₀‖ < δ →
      ∀ τ ∈ Ioo (-ε) ε,
        HasDerivAt (α (z₀, v₀))
          (geodesicFlowField (chartChristoffelField g x₀)
            (α (z₀, v₀) τ)) τ)
    (ht : t ∈ Ioo (-ε) ε) :
    (fun s : ℝ =>
      chartGeodesicMetric g x₀
        (α (z₀, v + s • w) t).1
        (α (z₀, v + s • w) t).2
        (α (z₀, v + s • w) t).2)
      =ᶠ[𝓝 (0 : ℝ)]
    (fun s : ℝ =>
      chartGeodesicMetric g x₀ z₀ (v + s • w) (v + s • w)) := by
  have hvel_eventually :
      ∀ᶠ s in 𝓝 (0 : ℝ), ‖v + s • w‖ < δ :=
    eventually_norm_add_smul_lt (v := v) (w := w) hv
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  filter_upwards [hvel_eventually] with s hs
  have hconst :=
    chart_geodesic_speed_constantOn_Ioo
      (g := g) (x₀ := x₀)
      (a := -ε) (b := ε)
      (γ := α (z₀, v + s • w))
      (hode (v + s • w) hs) ht hzero
  have h0 := hinit (v + s • w) hs
  simpa [h0] using hconst

omit [T2Space M] in
/--
The pointwise transverse pairing derivative has initial radial slope.  The
proof identifies the transverse identity's speed derivative with the derivative
of the initial-speed scalar by the flow derivative and constant speed.
-/
theorem chart_initialVelocity_transverse_pairing_hasDerivAt_initialSlope
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E} {t : ℝ}
    (hbase : HasDerivAt (α (z₀, v))
      (geodesicFlowField (chartChristoffelField g x₀)
        (α (z₀, v) t)) t)
    (hΨ : HasDerivAt Ψ
      (linearizedGeodesicFlowFieldAlong
        (chartChristoffelField g x₀) (α (z₀, v)) t (Ψ t)) t)
    (hflow : HasDerivAt
      (fun s : ℝ => α (z₀, v + s • w) t) (Ψ t) 0)
    (hspeed_const :
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + s • w) t).1
          (α (z₀, v + s • w) t).2
          (α (z₀, v + s • w) t).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + s • w) (v + s • w)))
    (hGd_base : DifferentiableAt ℝ (chartGeodesicMetric g x₀)
      (α (z₀, v) t).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀) :
    HasDerivAt
      (fun τ : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v) τ).1 (Ψ τ).1 (α (z₀, v) τ).2)
      (chartGeodesicMetric g x₀ z₀ v w) t := by
  let speedDeriv : ℝ :=
    ((fderiv ℝ (chartGeodesicMetric g x₀) (α (z₀, v) t).1)
      (Ψ t).1)
      (α (z₀, v) t).2 (α (z₀, v) t).2 +
    chartGeodesicMetric g x₀ (α (z₀, v) t).1
      (Ψ t).2 (α (z₀, v) t).2 +
    chartGeodesicMetric g x₀ (α (z₀, v) t).1
      (α (z₀, v) t).2 (Ψ t).2
  have hspeed_flow :
      HasDerivAt
        (fun s : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v + s • w) t).1
            (α (z₀, v + s • w) t).2
            (α (z₀, v + s • w) t).2)
        speedDeriv 0 := by
    simpa [speedDeriv] using
      chart_initialVelocity_speed_hasDerivAt_of_flowDerivative
        (g := g) (x₀ := x₀) (α := α)
        (z₀ := z₀) (v := v) (w := w) (Ψ := Ψ) (t := t)
        hflow hGd_base
  have hspeed_initial :
      HasDerivAt
        (fun s : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v + s • w) t).1
            (α (z₀, v + s • w) t).2
            (α (z₀, v + s • w) t).2)
        (chartGeodesicMetric g x₀ z₀ w v +
          chartGeodesicMetric g x₀ z₀ v w) 0 :=
    (chart_initialVelocity_initialSpeed_hasDerivAt
      (g := g) (x₀ := x₀) (z₀ := z₀) (v := v) (w := w)
      hGd_initial).congr_of_eventuallyEq hspeed_const
  have hspeed_eq :
      speedDeriv =
        chartGeodesicMetric g x₀ z₀ w v +
          chartGeodesicMetric g x₀ z₀ v w :=
    hspeed_flow.unique hspeed_initial
  have hJ :
      HasDerivAt (fun τ : ℝ => (Ψ τ).1) (Ψ t).2 t :=
    chart_linearized_fst_hasDerivAt
      (g := g) (x₀ := x₀) (γ := α (z₀, v)) (Ψ := Ψ) hΨ
  have hpair :
      HasDerivAt
        (fun τ : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v) τ).1 (Ψ τ).1 (α (z₀, v) τ).2)
        ((1 / 2 : ℝ) * speedDeriv) t := by
    simpa [speedDeriv] using
      chart_geodesic_transverse_pairing_hasDerivAt
        (g := g) (x₀ := x₀)
        (z := fun τ : ℝ => (α (z₀, v) τ).1)
        (v := fun τ : ℝ => (α (z₀, v) τ).2)
        (J := fun τ : ℝ => (Ψ τ).1)
        (t := t) (K := (Ψ t).2)
        (geodesic_position_hasDerivAt
          (Γ := chartChristoffelField g x₀) hbase)
        (geodesic_velocity_hasDerivAt
          (Γ := chartChristoffelField g x₀) hbase)
        hJ hGd_base
  have hsymm :
      chartGeodesicMetric g x₀ z₀ w v =
        chartGeodesicMetric g x₀ z₀ v w :=
    chartGeodesicMetric_symm g x₀ z₀ w v
  convert hpair using 1
  rw [hspeed_eq, hsymm]
  ring

omit [T2Space M] in
/--
Integrating a constant-slope transverse pairing derivative on a connected open
interval.  For the radial initial-velocity variation the initial pairing is
zero because `Ψ 0 = (0, w)`.
-/
theorem chart_initialVelocity_transverse_pairing_eq_t_mul_initial
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {a b t : ℝ}
    (hpair_deriv : ∀ τ ∈ Ioo a b,
      HasDerivAt
        (fun r : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v) r).1 (Ψ r).1 (α (z₀, v) r).2)
        (chartGeodesicMetric g x₀ z₀ v w) τ)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (ht : t ∈ Ioo a b) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 =
      t * chartGeodesicMetric g x₀ z₀ v w := by
  let slope : ℝ := chartGeodesicMetric g x₀ z₀ v w
  let pairing : ℝ → ℝ :=
    fun r : ℝ =>
      chartGeodesicMetric g x₀
        (α (z₀, v) r).1 (Ψ r).1 (α (z₀, v) r).2
  let adjusted : ℝ → ℝ := fun r : ℝ => pairing r - r * slope
  have hadj_deriv : ∀ r ∈ Ioo a b, HasDerivAt adjusted 0 r := by
    intro r hr
    have hlin : HasDerivAt (fun q : ℝ => q * slope) slope r :=
      hasDerivAt_mul_const slope
    simpa [adjusted, pairing, slope] using (hpair_deriv r hr).sub hlin
  have hadj_diff : DifferentiableOn ℝ adjusted (Ioo a b) :=
    fun r hr => (hadj_deriv r hr).differentiableAt.differentiableWithinAt
  have hadj_deriv_eq : (Ioo a b).EqOn (deriv adjusted) 0 :=
    fun r hr => (hadj_deriv r hr).deriv
  have hconst :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hadj_diff hadj_deriv_eq ht h0
  have hadj0 : adjusted 0 = 0 := by
    simp [adjusted, pairing, slope, hα0, hΨ0]
  have htzero : adjusted t = 0 := by
    simpa [hadj0] using hconst
  have hsub : pairing t - t * slope = 0 := by
    simpa [adjusted] using htzero
  simpa [pairing, slope] using sub_eq_zero.mp hsub

omit [T2Space M] in
/--
Integrated transverse Gauss pairing law from the pointwise ingredient package
on a common open interval.
-/
theorem chart_initialVelocity_integrated_transverse_gauss
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {a b t : ℝ}
    (hbase : ∀ τ ∈ Ioo a b,
      HasDerivAt (α (z₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (z₀, v) τ)) τ)
    (hΨ : ∀ τ ∈ Ioo a b,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) (α (z₀, v)) τ (Ψ τ)) τ)
    (hflow : ∀ τ ∈ Ioo a b,
      HasDerivAt
        (fun s : ℝ => α (z₀, v + s • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Ioo a b,
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + s • w) τ).1
          (α (z₀, v + s • w) τ).2
          (α (z₀, v + s • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + s • w) (v + s • w)))
    (hGd_base : ∀ τ ∈ Ioo a b,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (ht : t ∈ Ioo a b) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 =
      t * chartGeodesicMetric g x₀ z₀ v w := by
  refine
    chart_initialVelocity_transverse_pairing_eq_t_mul_initial
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ)
      (a := a) (b := b) (t := t) ?_ hα0 hΨ0 h0 ht
  intro τ hτ
  exact
    chart_initialVelocity_transverse_pairing_hasDerivAt_initialSlope
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (t := τ)
      (hbase τ hτ) (hΨ τ hτ) (hflow τ hτ)
      (hspeed_const τ hτ) (hGd_base τ hτ) hGd_initial

omit [T2Space M] in
/--
Orthogonal integrated transverse Gauss lemma in chart form for the radial
initial-velocity variation.
-/
theorem chart_initialVelocity_integrated_transverse_gauss_orthogonal
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {a b t : ℝ}
    (hbase : ∀ τ ∈ Ioo a b,
      HasDerivAt (α (z₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (z₀, v) τ)) τ)
    (hΨ : ∀ τ ∈ Ioo a b,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) (α (z₀, v)) τ (Ψ τ)) τ)
    (hflow : ∀ τ ∈ Ioo a b,
      HasDerivAt
        (fun s : ℝ => α (z₀, v + s • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Ioo a b,
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + s • w) τ).1
          (α (z₀, v + s • w) τ).2
          (α (z₀, v + s • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + s • w) (v + s • w)))
    (hGd_base : ∀ τ ∈ Ioo a b,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (horth : chartGeodesicMetric g x₀ z₀ v w = 0)
    (ht : t ∈ Ioo a b) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 = 0 := by
  have hpair :=
    chart_initialVelocity_integrated_transverse_gauss
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (a := a) (b := b) (t := t)
      hbase hΨ hflow hspeed_const hGd_base hGd_initial
      hα0 hΨ0 h0 ht
  simpa [horth] using hpair

end GeodesicTransport
end Poincare
