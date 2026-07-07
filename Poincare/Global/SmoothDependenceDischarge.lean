import Poincare.Global.GaussLemmaIntegrated

/-!
# Smooth-dependence payload discharge

This module records the non-vacuous payload now available from the proven
initial-velocity flow derivative.  The older
`ChartGeodesicInitialVelocitySmoothDependence` interface asked for a smooth
two-parameter geodesic family; the transverse Gauss consumers actually need
the following pointwise facts:

* fixed-time `s`-derivatives of position and velocity in the initial-velocity
  family;
* the mixed-derivative commutation `∂ₜ J = K`;
* the transverse Gauss pointwise identity assembled from those derivatives.

The first item is supplied by
`chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`.
The second is the first component of the linearized geodesic equation, already
exported as `chart_linearized_fst_hasDerivAt`.
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
Payload map, fixed-time part: the proven uniform flow derivative gives the
variation derivative of the whole first-order chart state and therefore of
both position and velocity components.
-/
theorem chart_initialVelocity_fixedTime_payload_of_uniform_geodesicFlow
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
    (ht : t ∈ Icc (0 : ℝ) ε) :
    HasDerivAt
        (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) t)
        (Ψ t) 0 ∧
      HasDerivAt
        (fun s : ℝ => (α (extChartAt I x₀ x₀, v + s • w) t).1)
        (Ψ t).1 0 ∧
      HasDerivAt
        (fun s : ℝ => (α (extChartAt I x₀ x₀, v + s • w) t).2)
        (Ψ t).2 0 := by
  have hflow :
      HasDerivAt
        (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) t)
        (Ψ t) 0 :=
    chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := a)
      (α := α) (v := v) (w := w) (Ψ := Ψ)
      hε hv hα hΨ0 hΨder ht
  have hpos :
      HasDerivAt
        (fun s : ℝ => (α (extChartAt I x₀ x₀, v + s • w) t).1)
        (Ψ t).1 0 := by
    simpa using hflow.hasFDerivAt.fst.hasDerivAt
  have hvel :
      HasDerivAt
        (fun s : ℝ => (α (extChartAt I x₀ x₀, v + s • w) t).2)
        (Ψ t).2 0 := by
    simpa using hflow.hasFDerivAt.snd.hasDerivAt
  exact ⟨hflow, hpos, hvel⟩

omit [T2Space M] in
/--
Payload map, mixed-derivative part: on an interior point of the common time
interval, the linearized equation says that the derivative of the position
component `J = Ψ.1` is the velocity component `K = Ψ.2`.
-/
theorem chart_initialVelocity_mixedDerivative_payload_of_linearized
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε : ℝ} {α : E × E → ℝ → E × E}
    {v : E} {Ψ : ℝ → E × E} {t : ℝ}
    (hΨder : ∀ τ ∈ Icc (-ε) ε,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) τ (Ψ τ))
        (Icc (-ε) ε) τ)
    (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt (fun τ : ℝ => (Ψ τ).1) (Ψ t).2 t := by
  have ht_closed : t ∈ Icc (-ε) ε := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hnhds : Icc (-ε) ε ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hΨ :
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) t (Ψ t)) t :=
    (hΨder t ht_closed).hasDerivAt hnhds
  exact chart_linearized_fst_hasDerivAt
    (g := g) (x₀ := x₀)
    (γ := α (extChartAt I x₀ x₀, v)) (Ψ := Ψ) hΨ

omit [T2Space M] in
/--
Combined pointwise discharge of the de-facto payload consumed by
`GaussLemmaTransverse`: fixed-time `s`-derivatives, mixed derivative, and the
resulting pointwise transverse Gauss identity at `s = 0`.
-/
theorem chart_initialVelocity_transverse_variation_identity_of_uniform_geodesicFlow
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
    (ht_pos : t ∈ Ioo (0 : ℝ) ε)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀)
      (α (extChartAt I x₀ x₀, v) t).1) :
    ∃ pairDeriv speedDeriv : ℝ,
      HasDerivAt
        (fun τ : ℝ =>
          chartGeodesicMetric g x₀
            (α (extChartAt I x₀ x₀, v) τ).1 (Ψ τ).1
            (α (extChartAt I x₀ x₀, v) τ).2)
        pairDeriv t ∧
      HasDerivAt
        (fun s : ℝ =>
          chartGeodesicMetric g x₀
            (α (extChartAt I x₀ x₀, v + s • w) t).1
            (α (extChartAt I x₀ x₀, v + s • w) t).2
            (α (extChartAt I x₀ x₀, v + s • w) t).2)
        speedDeriv 0 ∧
      pairDeriv = (1 / 2 : ℝ) * speedDeriv := by
  have ht_closed_pos : t ∈ Icc (0 : ℝ) ε :=
    ⟨le_of_lt ht_pos.1, le_of_lt ht_pos.2⟩
  have ht_full_open : t ∈ Ioo (-ε) ε := by
    constructor
    · linarith [hε, ht_pos.1]
    · exact ht_pos.2
  have ht_full_closed : t ∈ Icc (-ε) ε :=
    ⟨le_of_lt ht_full_open.1, le_of_lt ht_full_open.2⟩
  have hnhds : Icc (-ε) ε ∈ 𝓝 t :=
    Icc_mem_nhds ht_full_open.1 ht_full_open.2
  have hbase :
      HasDerivAt (α (extChartAt I x₀ x₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v) t)) t :=
    ((hα v hv).2.1 t ht_full_closed).hasDerivAt hnhds
  have hpayload :=
    chart_initialVelocity_fixedTime_payload_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := a)
      (α := α) (v := v) (w := w) (Ψ := Ψ) (t := t)
      hε hv hα hΨ0 hΨder ht_closed_pos
  have hJ :
      HasDerivAt (fun τ : ℝ => (Ψ τ).1) (Ψ t).2 t :=
    chart_initialVelocity_mixedDerivative_payload_of_linearized
      (g := g) (x₀ := x₀) (ε := ε)
      (α := α) (v := v) (Ψ := Ψ) (t := t) hΨder ht_full_open
  rcases chart_geodesic_transverse_variation_identity
      (g := g) (x₀ := x₀)
      (Φ := fun s τ : ℝ => α (extChartAt I x₀ x₀, v + s • w) τ)
      (J := fun τ : ℝ => (Ψ τ).1)
      (K := fun τ : ℝ => (Ψ τ).2)
      (s := 0) (t := t)
      (by simpa using hbase) hJ hpayload.2.1 hpayload.2.2 (by simpa using hGd) with
    ⟨pairDeriv, speedDeriv, hpair, hspeed, hEq⟩
  refine ⟨pairDeriv, speedDeriv, ?_, hspeed, hEq⟩
  simpa using hpair

omit [T2Space M] in
/--
Discharge package from the exported uniform PL chart flow.  This is the
replacement for treating `ChartGeodesicInitialVelocitySmoothDependence` as a
black box: the common flow is the one exported by `expAt`, and for every
linearized solution `Ψ` the fixed-time and mixed-derivative payloads produce
the pointwise transverse identity.
-/
theorem exists_uniform_chart_initialVelocity_payload_package
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E,
        (∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) t))
                (Icc (-ε) ε) t) ∧
            (∀ t ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, v₀) t ∈
                closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
            (∀ t ∈ Icc (-ε) ε,
              (α (extChartAt I x₀ x₀, v₀) t).1 ∈
                (extChartAt I x₀).target) ∧
            ∀ s ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, s • v₀) σ =
                ((α (extChartAt I x₀ x₀, v₀) (s * σ)).1,
                  s • (α (extChartAt I x₀ x₀, v₀) (s * σ)).2)) ∧
        (∀ {v w : E} {Ψ : ℝ → E × E} {t : ℝ},
          ‖v‖ < δ →
          Ψ 0 = ((0 : E), w) →
          (∀ τ ∈ Icc (-ε) ε,
            HasDerivWithinAt Ψ
              (linearizedGeodesicFlowFieldAlong
                (chartChristoffelField g x₀)
                (α (extChartAt I x₀ x₀, v)) τ (Ψ τ))
              (Icc (-ε) ε) τ) →
          t ∈ Ioo (0 : ℝ) ε →
          DifferentiableAt ℝ (chartGeodesicMetric g x₀)
            (α (extChartAt I x₀ x₀, v) t).1 →
          ∃ pairDeriv speedDeriv : ℝ,
            HasDerivAt
              (fun τ : ℝ =>
                chartGeodesicMetric g x₀
                  (α (extChartAt I x₀ x₀, v) τ).1 (Ψ τ).1
                  (α (extChartAt I x₀ x₀, v) τ).2)
              pairDeriv t ∧
            HasDerivAt
              (fun s : ℝ =>
                chartGeodesicMetric g x₀
                  (α (extChartAt I x₀ x₀, v + s • w) t).1
                  (α (extChartAt I x₀ x₀, v + s • w) t).2
                  (α (extChartAt I x₀ x₀, v + s • w) t).2)
              speedDeriv 0 ∧
            pairDeriv = (1 / 2 : ℝ) * speedDeriv) := by
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, ε, hε, a, α, hα, _hexp⟩
  refine ⟨τ, hτ, δ, hδ, ε, hε, a, α, hα, ?_⟩
  intro v w Ψ t hv hΨ0 hΨder ht hGd
  have hαshort : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ τ ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) τ))
            (Icc (-ε) ε) τ) ∧
        ∀ τ ∈ Icc (-ε) ε,
          α (extChartAt I x₀ x₀, v₀) τ ∈
            closedBall (extChartAt I x₀ x₀, (0 : E)) a := by
    intro v₀ hv₀
    exact ⟨(hα v₀ hv₀).1, (hα v₀ hv₀).2.1, (hα v₀ hv₀).2.2.1⟩
  exact
    chart_initialVelocity_transverse_variation_identity_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := a)
      (α := α) (v := v) (w := w) (Ψ := Ψ) (t := t)
      hε hv hαshort hΨ0 hΨder ht hGd

omit [T2Space M] in
/--
The integrated transverse Gauss theorem with the smooth-dependence payload
spelled as explicit, non-vacuous hypotheses.  The previous lemmas discharge
`hflow` and the mixed-derivative component from the proven flow derivative on
positive fixed times; a full endpoint source expansion still needs these
interval hypotheses synchronized with the Jacobi oscillator and endpoint
chart-metric package.
-/
theorem chart_initialVelocity_integrated_transverse_gauss_payload
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
      t * chartGeodesicMetric g x₀ z₀ v w :=
  chart_initialVelocity_integrated_transverse_gauss
    (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
    (v := v) (w := w) (Ψ := Ψ) (a := a) (b := b) (t := t)
    hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 h0 ht

end GeodesicTransport
end Poincare
