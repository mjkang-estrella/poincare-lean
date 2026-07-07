import Poincare.Global.OrthogonalityFeed

/-!
# One-sided transverse Gauss payload

This module supplies the one-sided version of the payload-fed transverse Gauss
integration used by the orthogonality feed.  The older payload consumer asks
for time derivatives on an open interval containing `0`; the hosted exports
available downstream are closed-interval, one-sided facts on `Icc 0 T`.

The statements below keep the same non-vacuous payload fields, but replace the
time ODE hypotheses by `HasDerivWithinAt ... (Icc 0 T)`.  The scalar
integration step uses convexity of `Icc 0 T` and `fderivWithin = 0`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 900000

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

namespace GeodesicTransport

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/-- First-component projection of a chart geodesic equation within a time set. -/
theorem geodesic_position_hasDerivWithinAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E}
    {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ (geodesicFlowField Γ (γ t)) s t) :
    HasDerivWithinAt (fun τ : ℝ => (γ τ).1) (γ t).2 s t := by
  simpa [geodesicFlowField] using hγ.hasFDerivWithinAt.fst.hasDerivWithinAt

omit [T2Space M] in
/-- Second-component projection of a chart geodesic equation within a time set. -/
theorem geodesic_velocity_hasDerivWithinAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E}
    {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ (geodesicFlowField Γ (γ t)) s t) :
    HasDerivWithinAt (fun τ : ℝ => (γ τ).2)
      (-(Γ (γ t).1) (γ t).2 (γ t).2) s t := by
  simpa [geodesicFlowField] using hγ.hasFDerivWithinAt.snd.hasDerivWithinAt

omit [T2Space M] in
/-- The first component of a chart linearized solution has within-derivative equal to the second. -/
theorem chart_linearized_fst_hasDerivWithinAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {γ Ψ : ℝ → E × E} {s : Set ℝ} {t : ℝ}
    (hΨ : HasDerivWithinAt Ψ
      (linearizedGeodesicFlowFieldAlong
        (chartChristoffelField g x₀) γ t (Ψ t)) s t) :
    HasDerivWithinAt (fun τ : ℝ => (Ψ τ).1) (Ψ t).2 s t := by
  have hfst := hΨ.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa [chart_linearizedGeodesicFlowFieldAlong_fst (g := g) (x₀ := x₀)
    (γ := γ) (t := t) (ψ := Ψ t)] using hfst

omit [T2Space M] in
/--
Derivative within a closed time interval of the transverse metric pairing
along a chart geodesic.
-/
theorem chart_geodesic_transverse_pairing_hasDerivWithinAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z v J : ℝ → E} {s : Set ℝ} {t : ℝ} {K : E}
    (hz : HasDerivWithinAt z (v t) s t)
    (hv : HasDerivWithinAt v
      (-(chartChristoffelField g x₀ (z t)) (v t) (v t)) s t)
    (hJ : HasDerivWithinAt J K s t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z t)) :
    HasDerivWithinAt
      (fun τ : ℝ => chartGeodesicMetric g x₀ (z τ) (J τ) (v τ))
      ((1 / 2 : ℝ) *
        (((fderiv ℝ (chartGeodesicMetric g x₀) (z t)) (J t)) (v t) (v t) +
          chartGeodesicMetric g x₀ (z t) K (v t) +
            chartGeodesicMetric g x₀ (z t) (v t) K)) s t := by
  set G := chartGeodesicMetric g x₀
  set Γ : E := (chartChristoffelField g x₀ (z t)) (v t) (v t)
  have hGpath :
      HasDerivWithinAt
        (fun τ : ℝ => G (z τ))
        ((fderiv ℝ G (z t)) (v t)) s t := by
    have hcomp :
        HasDerivWithinAt (G ∘ z) ((fderiv ℝ G (z t)) (v t)) s t :=
      HasFDerivAt.comp_hasDerivWithinAt
        (𝕜 := ℝ) (F := E)
        (f := z) (f' := v t) (x := t)
        (l := G) (l' := fderiv ℝ G (z t)) hGd.hasFDerivAt hz
    simpa [Function.comp_def] using hcomp
  have hGJ :
      HasDerivWithinAt
        (fun τ : ℝ => G (z τ) (J τ))
        (((fderiv ℝ G (z t)) (v t)) (J t) + G (z t) K) s t := by
    simpa using hGpath.clm_apply hJ
  have hraw :
      HasDerivWithinAt
        (fun τ : ℝ => G (z τ) (J τ) (v τ))
        ((((fderiv ℝ G (z t)) (v t)) (J t) + G (z t) K) (v t) +
          G (z t) (J t) (-Γ)) s t := by
    simpa [Γ] using hGJ.clm_apply hv
  have hΓpair : G (z t) Γ (J t) =
      (1 / 2 : ℝ) *
        (((fderiv ℝ G (z t)) (v t)) (v t) (J t) +
          ((fderiv ℝ G (z t)) (v t)) (v t) (J t) -
            ((fderiv ℝ G (z t)) (J t)) (v t) (v t)) := by
    have h := chartChristoffelField_pairing_eq_blendedChartMetric
      (g := g) (x₀ := x₀) (z := z t) (u := v t) (v := v t) (w := J t)
    simpa [G, Γ] using h
  have hsymmΓ : G (z t) (J t) Γ = G (z t) Γ (J t) := by
    simpa [G] using chartGeodesicMetric_symm
      (g := g) (x₀ := x₀) (z := z t) (v := J t) (w := Γ)
  have hdsymm : ((fderiv ℝ G (z t)) (v t)) (J t) (v t) =
      ((fderiv ℝ G (z t)) (v t)) (v t) (J t) := by
    exact CovariantDerivative.fderiv_metric_symm G hGd
      (fun y p q => by
        simpa [G] using chartGeodesicMetric_symm (g := g) (x₀ := x₀) y p q)
      (v t) (J t) (v t)
  have hGKV : G (z t) (v t) K = G (z t) K (v t) := by
    simpa [G] using chartGeodesicMetric_symm
      (g := g) (x₀ := x₀) (z := z t) (v := v t) (w := K)
  convert hraw using 1
  simp only [ContinuousLinearMap.add_apply, map_neg]
  rw [hsymmΓ, hΓpair, hdsymm, hGKV]
  ring

omit [T2Space M] in
/--
Pointwise transverse pairing slope from one-sided time-derivative payloads.
-/
theorem chart_initialVelocity_transverse_pairing_hasDerivWithinAt_initialSlope
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {s : Set ℝ} {t : ℝ}
    (hbase : HasDerivWithinAt (α (z₀, v))
      (geodesicFlowField (chartChristoffelField g x₀)
        (α (z₀, v) t)) s t)
    (hΨ : HasDerivWithinAt Ψ
      (linearizedGeodesicFlowFieldAlong
        (chartChristoffelField g x₀) (α (z₀, v)) t (Ψ t)) s t)
    (hflow : HasDerivAt
      (fun r : ℝ => α (z₀, v + r • w) t) (Ψ t) 0)
    (hspeed_const :
      (fun r : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + r • w) t).1
          (α (z₀, v + r • w) t).2
          (α (z₀, v + r • w) t).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + r • w) (v + r • w)))
    (hGd_base : DifferentiableAt ℝ (chartGeodesicMetric g x₀)
      (α (z₀, v) t).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀) :
    HasDerivWithinAt
      (fun τ : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v) τ).1 (Ψ τ).1 (α (z₀, v) τ).2)
      (chartGeodesicMetric g x₀ z₀ v w) s t := by
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
        (fun r : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v + r • w) t).1
            (α (z₀, v + r • w) t).2
            (α (z₀, v + r • w) t).2)
        speedDeriv 0 := by
    simpa [speedDeriv] using
      chart_initialVelocity_speed_hasDerivAt_of_flowDerivative
        (g := g) (x₀ := x₀) (α := α)
        (z₀ := z₀) (v := v) (w := w) (Ψ := Ψ) (t := t)
        hflow hGd_base
  have hspeed_initial :
      HasDerivAt
        (fun r : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v + r • w) t).1
            (α (z₀, v + r • w) t).2
            (α (z₀, v + r • w) t).2)
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
      HasDerivWithinAt (fun τ : ℝ => (Ψ τ).1) (Ψ t).2 s t :=
    chart_linearized_fst_hasDerivWithinAt
      (g := g) (x₀ := x₀) (γ := α (z₀, v)) (Ψ := Ψ) hΨ
  have hpair :
      HasDerivWithinAt
        (fun τ : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v) τ).1 (Ψ τ).1 (α (z₀, v) τ).2)
        ((1 / 2 : ℝ) * speedDeriv) s t := by
    simpa [speedDeriv] using
      chart_geodesic_transverse_pairing_hasDerivWithinAt
        (g := g) (x₀ := x₀)
        (z := fun τ : ℝ => (α (z₀, v) τ).1)
        (v := fun τ : ℝ => (α (z₀, v) τ).2)
        (J := fun τ : ℝ => (Ψ τ).1)
        (s := s) (t := t) (K := (Ψ t).2)
        (geodesic_position_hasDerivWithinAt
          (Γ := chartChristoffelField g x₀) hbase)
        (geodesic_velocity_hasDerivWithinAt
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
Integrating a constant-slope transverse pairing derivative on `Icc 0 T`.
The initial pairing is zero because `Ψ 0 = (0, w)`.
-/
theorem chart_initialVelocity_transverse_pairing_eq_t_mul_initial_on_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {T t : ℝ} (hT : 0 < T)
    (hpair_deriv : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (fun r : ℝ =>
          chartGeodesicMetric g x₀
            (α (z₀, v) r).1 (Ψ r).1 (α (z₀, v) r).2)
        (chartGeodesicMetric g x₀ z₀ v w) (Icc (0 : ℝ) T) τ)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (ht : t ∈ Icc (0 : ℝ) T) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 =
      t * chartGeodesicMetric g x₀ z₀ v w := by
  let slope : ℝ := chartGeodesicMetric g x₀ z₀ v w
  let pairing : ℝ → ℝ :=
    fun r : ℝ =>
      chartGeodesicMetric g x₀
        (α (z₀, v) r).1 (Ψ r).1 (α (z₀, v) r).2
  let adjusted : ℝ → ℝ := fun r : ℝ => pairing r - r * slope
  have hadj_deriv : ∀ r ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt adjusted 0 (Icc (0 : ℝ) T) r := by
    intro r hr
    have hlin : HasDerivWithinAt (fun q : ℝ => q * slope) slope
        (Icc (0 : ℝ) T) r :=
      (hasDerivAt_mul_const slope (x := r)).hasDerivWithinAt
    simpa [adjusted, pairing, slope] using (hpair_deriv r hr).sub hlin
  have hadj_diff : DifferentiableOn ℝ adjusted (Icc (0 : ℝ) T) :=
    fun r hr => (hadj_deriv r hr).differentiableWithinAt
  have hadj_fderiv_eq :
      ∀ r ∈ Icc (0 : ℝ) T,
        fderivWithin ℝ adjusted (Icc (0 : ℝ) T) r = 0 := by
    intro r hr
    have huniq : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) T) r :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt hr
    simpa using (hadj_deriv r hr).hasFDerivWithinAt.fderivWithin huniq
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_of_lt hT⟩
  have hconst :=
    (convex_Icc (0 : ℝ) T).is_const_of_fderivWithin_eq_zero
      hadj_diff hadj_fderiv_eq ht hzero
  have hadj0 : adjusted 0 = 0 := by
    simp [adjusted, pairing, slope, hα0, hΨ0]
  have htzero : adjusted t = 0 := by
    simpa [hadj0] using hconst
  have hsub : pairing t - t * slope = 0 := by
    simpa [adjusted] using htzero
  simpa [pairing, slope] using sub_eq_zero.mp hsub

omit [T2Space M] in
/--
Integrated transverse Gauss law on the one-sided interval `Icc 0 T`.
-/
theorem chart_initialVelocity_integrated_transverse_gauss_oneSided
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {T t : ℝ} (hT : 0 < T)
    (hbase : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (α (z₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (z₀, v) τ)) (Icc (0 : ℝ) T) τ)
    (hΨ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) (α (z₀, v)) τ (Ψ τ))
        (Icc (0 : ℝ) T) τ)
    (hflow : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ => α (z₀, v + r • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + r • w) τ).1
          (α (z₀, v + r • w) τ).2
          (α (z₀, v + r • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + r • w) (v + r • w)))
    (hGd_base : ∀ τ ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (ht : t ∈ Icc (0 : ℝ) T) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 =
      t * chartGeodesicMetric g x₀ z₀ v w := by
  refine
    chart_initialVelocity_transverse_pairing_eq_t_mul_initial_on_Icc
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (T := T) (t := t) hT ?_
      hα0 hΨ0 ht
  intro τ hτ
  exact
    chart_initialVelocity_transverse_pairing_hasDerivWithinAt_initialSlope
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (s := Icc (0 : ℝ) T) (t := τ)
      (hbase τ hτ) (hΨ τ hτ) (hflow τ hτ)
      (hspeed_const τ hτ) (hGd_base τ hτ) hGd_initial

omit [T2Space M] in
/-- Orthogonal specialization of the one-sided integrated transverse Gauss law. -/
theorem chart_initialVelocity_integrated_transverse_gauss_oneSided_orthogonal
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {T t : ℝ} (hT : 0 < T)
    (hbase : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (α (z₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (z₀, v) τ)) (Icc (0 : ℝ) T) τ)
    (hΨ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) (α (z₀, v)) τ (Ψ τ))
        (Icc (0 : ℝ) T) τ)
    (hflow : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ => α (z₀, v + r • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + r • w) τ).1
          (α (z₀, v + r • w) τ).2
          (α (z₀, v + r • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + r • w) (v + r • w)))
    (hGd_base : ∀ τ ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (horth : chartGeodesicMetric g x₀ z₀ v w = 0)
    (ht : t ∈ Icc (0 : ℝ) T) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 = 0 := by
  have hpair :=
    chart_initialVelocity_integrated_transverse_gauss_oneSided
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (T := T) (t := t) hT
      hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 ht
  simpa [horth] using hpair

end GeodesicTransport

namespace OrthogonalityFeed

variable {M3 : Type u}
variable [TopologicalSpace M3] [T2Space M3]
variable [ChartedSpace E3 M3]
variable [IsManifold I3 ∞ M3]

open GeodesicTransport

omit [T2Space M3] in
/--
Chart-metric transverse orthogonality from a one-sided payload on `Icc 0 T`.
-/
theorem chartMetric_initialVelocity_integrated_transverse_gauss_oneSided_orthogonal
    (g : ClosedSmoothRiemannianMetric 3 M3) (x₀ : M3)
    {α : E3 × E3 → ℝ → E3 × E3} {z₀ v w : E3} {Ψ : ℝ → E3 × E3}
    {T t : ℝ} (hT : 0 < T)
    (hbase : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (α (z₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (z₀, v) τ)) (Icc (0 : ℝ) T) τ)
    (hΨ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) (α (z₀, v)) τ (Ψ τ))
        (Icc (0 : ℝ) T) τ)
    (hflow : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ => α (z₀, v + r • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + r • w) τ).1
          (α (z₀, v + r • w) τ).2
          (α (z₀, v + r • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + r • w) (v + r • w)))
    (hGd_base : ∀ τ ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    (horth : chartGeodesicMetric g x₀ z₀ v w = 0)
    (ht : t ∈ Icc (0 : ℝ) T)
    (hcut : cutoff (n := 3) x₀ (α (z₀, v) t).1 = 1) :
    CovariantDerivative.chartMetric g.inner x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 = 0 := by
  have hblend :=
    chart_initialVelocity_integrated_transverse_gauss_oneSided_orthogonal
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (T := T) (t := t) hT
      hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 horth ht
  have hmetric :
      chartGeodesicMetric g x₀ (α (z₀, v) t).1 =
        CovariantDerivative.chartMetric g.inner x₀ (α (z₀, v) t).1 := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
      (g := g) (x₀ := x₀) hcut)
  rw [hmetric] at hblend
  simpa using hblend

omit [T2Space M3] in
/--
Source-anchor transverse `horth` on the one-sided hosted payload interval.
-/
theorem source_transverse_horth_on_Icc_of_oneSided_payload
    (g : ClosedSmoothRiemannianMetric 3 M3) (x₀ : M3)
    {α : E3 × E3 → ℝ → E3 × E3} {v w : E3} {Ψ : ℝ → E3 × E3}
    {T : ℝ} (hT : 0 < T)
    (hbase : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v) τ)) (Icc (0 : ℝ) T) τ)
    (hΨ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v)) τ (Ψ τ))
        (Icc (0 : ℝ) T) τ)
    (hflow : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ => α (extChartAt I3 x₀ x₀, v + r • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        chartGeodesicMetric g x₀
          (α (extChartAt I3 x₀ x₀, v + r • w) τ).1
          (α (extChartAt I3 x₀ x₀, v + r • w) τ).2
          (α (extChartAt I3 x₀ x₀, v + r • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (v + r • w) (v + r • w)))
    (hGd_base : ∀ τ ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀)
        (α (extChartAt I3 x₀ x₀, v) τ).1)
    (hGd_initial :
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (extChartAt I3 x₀ x₀))
    (hα0 : α (extChartAt I3 x₀ x₀, v) 0 = (extChartAt I3 x₀ x₀, v))
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    (horth : CartanMap.sourceAnchorChartMetric g x₀ v w = 0)
    (hcut : ∀ τ ∈ Icc (0 : ℝ) T,
      cutoff (n := 3) x₀ (α (extChartAt I3 x₀ x₀, v) τ).1 = 1) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I3 x₀ x₀, v) τ).1
        (Ψ τ).1 (α (extChartAt I3 x₀ x₀, v) τ).2 = 0 := by
  have hanchorCut : cutoff (n := 3) x₀ (extChartAt I3 x₀ x₀) = 1 :=
    (cutoff_eventuallyEq_one (n := 3) x₀).self_of_nhds
  have hanchorMetric :
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) =
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := x₀) hanchorCut)
  have horth_blended :
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) v w = 0 := by
    rw [hanchorMetric]
    simpa [CartanMap.sourceAnchorChartMetric] using horth
  intro τ hτ
  exact
    chartMetric_initialVelocity_integrated_transverse_gauss_oneSided_orthogonal
      (g := g) (x₀ := x₀) (α := α) (z₀ := extChartAt I3 x₀ x₀)
      (v := v) (w := w) (Ψ := Ψ) (T := T) (t := τ) hT
      hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0
      horth_blended hτ (hcut τ hτ)

/-- Target-anchor transverse `horth`, specialized to the round sphere. -/
theorem target_transverse_horth_on_Icc_of_oneSided_payload
    (p₀ : RoundSphere3)
    {α : E3 × E3 → ℝ → E3 × E3} {v w : E3} {Ψ : ℝ → E3 × E3}
    {T : ℝ} (hT : 0 < T)
    (hbase : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (α (extChartAt I3 p₀ p₀, v))
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I3 p₀ p₀, v) τ)) (Icc (0 : ℝ) T) τ)
    (hΨ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I3 p₀ p₀, v)) τ (Ψ τ))
        (Icc (0 : ℝ) T) τ)
    (hflow : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ => α (extChartAt I3 p₀ p₀, v + r • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        chartGeodesicMetric roundSphereMetric3 p₀
          (α (extChartAt I3 p₀ p₀, v + r • w) τ).1
          (α (extChartAt I3 p₀ p₀, v + r • w) τ).2
          (α (extChartAt I3 p₀ p₀, v + r • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (v + r • w) (v + r • w)))
    (hGd_base : ∀ τ ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀)
        (α (extChartAt I3 p₀ p₀, v) τ).1)
    (hGd_initial :
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀)
        (extChartAt I3 p₀ p₀))
    (hα0 : α (extChartAt I3 p₀ p₀, v) 0 = (extChartAt I3 p₀ p₀, v))
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    (horth : CartanMap.targetAnchorChartMetric p₀ v w = 0)
    (hcut : ∀ τ ∈ Icc (0 : ℝ) T,
      cutoff (n := 3) p₀ (α (extChartAt I3 p₀ p₀, v) τ).1 = 1) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (α (extChartAt I3 p₀ p₀, v) τ).1
        (Ψ τ).1 (α (extChartAt I3 p₀ p₀, v) τ).2 = 0 := by
  exact
    source_transverse_horth_on_Icc_of_oneSided_payload
      (g := roundSphereMetric3) (x₀ := p₀) (α := α)
      (v := v) (w := w) (Ψ := Ψ) (T := T) hT
      hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0
      (by simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using horth)
      hcut

end OrthogonalityFeed
end Poincare
