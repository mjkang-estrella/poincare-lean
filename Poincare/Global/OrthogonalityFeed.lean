import Poincare.Global.SpeedGeneric
import Poincare.Global.SmoothDependenceDischarge

/-!
# Orthogonality feed for the speed-generic layer

The all-direction endpoint orthogonality hypothesis is too strong.  The
integrated transverse Gauss law gives the exact pairing

`G(γ t)(J t, γ' t) = t * G(z₀)(v, w)`.

Thus radial input `w = v` is pinned to `t * speed²`, while anchor-transverse
input gives the `horth` hypothesis needed by the speed-generic transverse
variants.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 900000

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace OrthogonalityFeed

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

open GeodesicTransport

/--
Radial pin for the all-direction claim.  Taking the initial-velocity variation
direction to be the radial velocity itself gives `t * speed²`, not zero.
-/
theorem chart_initialVelocity_radial_pairing_eq_t_mul_speed_sq_payload
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v : E} {Ψ : ℝ → E × E}
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
        (fun s : ℝ => α (z₀, v + s • v) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Ioo a b,
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + s • v) τ).1
          (α (z₀, v + s • v) τ).2
          (α (z₀, v + s • v) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + s • v) (v + s • v)))
    (hGd_base : ∀ τ ∈ Ioo a b,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), v))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (ht : t ∈ Ioo a b) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 =
      t * chartGeodesicMetric g x₀ z₀ v v :=
  chart_initialVelocity_integrated_transverse_gauss_payload
    (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
    (v := v) (w := v) (Ψ := Ψ) (a := a) (b := b) (t := t)
    hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 h0 ht

/--
Nonzero radial pin.  Under nonzero time and nonzero initial speed, the radial
member of the all-direction pairing cannot satisfy endpoint orthogonality.
-/
theorem chart_initialVelocity_radial_pairing_ne_zero_payload
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E} {z₀ v : E} {Ψ : ℝ → E × E}
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
        (fun s : ℝ => α (z₀, v + s • v) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Ioo a b,
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + s • v) τ).1
          (α (z₀, v + s • v) τ).2
          (α (z₀, v + s • v) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + s • v) (v + s • v)))
    (hGd_base : ∀ τ ∈ Ioo a b,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E), v))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (ht : t ∈ Ioo a b)
    (ht_ne : t ≠ 0)
    (hspeed_ne : chartGeodesicMetric g x₀ z₀ v v ≠ 0) :
    chartGeodesicMetric g x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 ≠ 0 := by
  rw [chart_initialVelocity_radial_pairing_eq_t_mul_speed_sq_payload
    (g := g) (x₀ := x₀) (α := α) (z₀ := z₀) (v := v) (Ψ := Ψ)
    (a := a) (b := b) (t := t)
    hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 h0 ht]
  exact mul_ne_zero ht_ne hspeed_ne

/-- Orthogonal specialization of the payload-fed integrated transverse Gauss law. -/
theorem chart_initialVelocity_integrated_transverse_gauss_payload_orthogonal
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
    chart_initialVelocity_integrated_transverse_gauss_payload
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (a := a) (b := b) (t := t)
      hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 h0 ht
  simpa [horth] using hpair

/--
Chart-metric version of the transverse payload: in the cutoff-one zone the
blended metric conclusion is exactly the transported chart metric `horth`.
-/
theorem chartMetric_initialVelocity_integrated_transverse_gauss_payload_orthogonal
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
    (ht : t ∈ Ioo a b)
    (hcut : cutoff (n := n) x₀ (α (z₀, v) t).1 = 1) :
    CovariantDerivative.chartMetric g.inner x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 = 0 := by
  have hblend :=
    chart_initialVelocity_integrated_transverse_gauss_payload_orthogonal
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (a := a) (b := b) (t := t)
      hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 h0 horth ht
  have hmetric :
      chartGeodesicMetric g x₀ (α (z₀, v) t).1 =
        CovariantDerivative.chartMetric g.inner x₀ (α (z₀, v) t).1 := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := x₀) hcut)
  rw [hmetric] at hblend
  simpa using hblend

section AnchorMetric

variable {M3 : Type u}
variable [TopologicalSpace M3] [T2Space M3]
variable [ChartedSpace E3 M3]
variable [IsManifold I3 ∞ M3]

/--
Source-anchor transverse `horth` on a closed interval lying inside the open
payload interval.
-/
theorem source_transverse_horth_on_Icc_of_payload
    (g : ClosedSmoothRiemannianMetric 3 M3) (x₀ : M3)
    {α : E3 × E3 → ℝ → E3 × E3} {v w : E3} {Ψ : ℝ → E3 × E3}
    {a b tmin tmax : ℝ}
    (hsub : Icc tmin tmax ⊆ Ioo a b)
    (hbase : ∀ τ ∈ Ioo a b,
      HasDerivAt (α (extChartAt I3 x₀ x₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v) τ)) τ)
    (hΨ : ∀ τ ∈ Ioo a b,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v)) τ (Ψ τ)) τ)
    (hflow : ∀ τ ∈ Ioo a b,
      HasDerivAt
        (fun s : ℝ => α (extChartAt I3 x₀ x₀, v + s • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Ioo a b,
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (extChartAt I3 x₀ x₀, v + s • w) τ).1
          (α (extChartAt I3 x₀ x₀, v + s • w) τ).2
          (α (extChartAt I3 x₀ x₀, v + s • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (v + s • w) (v + s • w)))
    (hGd_base : ∀ τ ∈ Ioo a b,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀)
        (α (extChartAt I3 x₀ x₀, v) τ).1)
    (hGd_initial :
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (extChartAt I3 x₀ x₀))
    (hα0 : α (extChartAt I3 x₀ x₀, v) 0 = (extChartAt I3 x₀ x₀, v))
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (horth : CartanMap.sourceAnchorChartMetric g x₀ v w = 0)
    (hcut : ∀ τ ∈ Icc tmin tmax,
      cutoff (n := 3) x₀ (α (extChartAt I3 x₀ x₀, v) τ).1 = 1) :
    ∀ τ ∈ Icc tmin tmax,
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
    chartMetric_initialVelocity_integrated_transverse_gauss_payload_orthogonal
      (g := g) (x₀ := x₀) (α := α) (z₀ := extChartAt I3 x₀ x₀)
      (v := v) (w := w) (Ψ := Ψ) (a := a) (b := b) (t := τ)
      hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 h0
      horth_blended (hsub hτ) (hcut τ hτ)

/-- Target-anchor transverse `horth`, specialized to the round sphere. -/
theorem target_transverse_horth_on_Icc_of_payload
    (p₀ : RoundSphere3)
    {α : E3 × E3 → ℝ → E3 × E3} {v w : E3} {Ψ : ℝ → E3 × E3}
    {a b tmin tmax : ℝ}
    (hsub : Icc tmin tmax ⊆ Ioo a b)
    (hbase : ∀ τ ∈ Ioo a b,
      HasDerivAt (α (extChartAt I3 p₀ p₀, v))
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I3 p₀ p₀, v) τ)) τ)
    (hΨ : ∀ τ ∈ Ioo a b,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I3 p₀ p₀, v)) τ (Ψ τ)) τ)
    (hflow : ∀ τ ∈ Ioo a b,
      HasDerivAt
        (fun s : ℝ => α (extChartAt I3 p₀ p₀, v + s • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Ioo a b,
      (fun s : ℝ =>
        chartGeodesicMetric roundSphereMetric3 p₀
          (α (extChartAt I3 p₀ p₀, v + s • w) τ).1
          (α (extChartAt I3 p₀ p₀, v + s • w) τ).2
          (α (extChartAt I3 p₀ p₀, v + s • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (v + s • w) (v + s • w)))
    (hGd_base : ∀ τ ∈ Ioo a b,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀)
        (α (extChartAt I3 p₀ p₀, v) τ).1)
    (hGd_initial :
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀)
        (extChartAt I3 p₀ p₀))
    (hα0 : α (extChartAt I3 p₀ p₀, v) 0 = (extChartAt I3 p₀ p₀, v))
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (horth : CartanMap.targetAnchorChartMetric p₀ v w = 0)
    (hcut : ∀ τ ∈ Icc tmin tmax,
      cutoff (n := 3) p₀ (α (extChartAt I3 p₀ p₀, v) τ).1 = 1) :
    ∀ τ ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (α (extChartAt I3 p₀ p₀, v) τ).1
        (Ψ τ).1 (α (extChartAt I3 p₀ p₀, v) τ).2 = 0 := by
  exact
    source_transverse_horth_on_Icc_of_payload
      (g := roundSphereMetric3) (x₀ := p₀) (α := α)
      (v := v) (w := w) (Ψ := Ψ) (a := a) (b := b)
      (tmin := tmin) (tmax := tmax)
      hsub hbase hΨ hflow hspeed_const hGd_base hGd_initial hα0 hΨ0 h0
      (by simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using horth)
      hcut

end AnchorMetric

end OrthogonalityFeed
end Poincare
