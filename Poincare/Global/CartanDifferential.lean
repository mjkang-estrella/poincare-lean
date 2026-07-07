import Poincare.Global.CartanPullback
import Poincare.Global.GaussLemmaRadial

/-!
# Endpoint differential surface for the Cartan map

This module packages the nonzero-endpoint differential ingredients used by the
Cartan local-isometry route.  The statements are deliberately chart-level:
they expose the radial ray derivative, the transverse `sin t / t` endpoint
factor, the Gauss cross-pairing, and the strict chain rule for

`expAtChart p₀ ∘ L ∘ (expAtChart x₀)⁻¹`.

The full pullback identity still depends on feeding the endpoint surface into
the two exponential charts.  The final section isolates the remaining algebra:
once both exponential differentials have the same radial/transverse scale
factors, rigid-9's Gram decomposition and tangent alignment give the metric
identity.
-/

noncomputable section

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanDifferential

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

section Endpoint

universe u

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Homogeneity bookkeeping for endpoint variations.  A velocity variation
`a • v + w` inside the time-`t` parameterization becomes a radial endpoint
variation with coefficient `a * t` plus the endpoint transverse vector `t • w`.
-/
theorem endpoint_decomposition_homogeneity
    (t a s : ℝ) (v w : E) :
    t • (v + s • (a • v + w)) =
      (t + s * (a * t)) • v + s • (t • w) := by
  module

/--
Radial endpoint derivative for the chart-read fixed-time exponential, stated
against the uniform PL-flow package exported by `ExponentialFixedTime`.

At the endpoint `expAt (t • v)`, changing the radial parameter by
`s ↦ t + s*c` differentiates to `c` times the chart geodesic velocity.
-/
theorem expAt_chart_radial_hasDerivAt_of_uniform_geodesicFlow
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ τ ε : ℝ}
    {α : E × E → ℝ → E × E}
    {v : E} {t c : ℝ}
    (hv : ‖v‖ < δ)
    (hαder : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) r))
        (Icc (-ε) ε) r)
    (hαtarget : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-ε) ε,
      (α (extChartAt I x₀ x₀, v₀) r).1 ∈ (extChartAt I x₀).target)
    (hexp : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (0 : ℝ) τ,
      GeodesicTransport.expAt g x₀ (r • v₀) =
        (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) r).1)
    (htτ : t ∈ Ioo (0 : ℝ) τ)
    (htε : t ∈ Ioo (-ε) ε) :
    HasDerivAt
      (fun s : ℝ =>
        extChartAt I x₀
          (GeodesicTransport.expAt g x₀ ((t + s * c) • v)))
      (c • (α (extChartAt I x₀ x₀, v) t).2) 0 := by
  have htε_closed : t ∈ Icc (-ε) ε := ⟨le_of_lt htε.1, le_of_lt htε.2⟩
  have hIccε_nhds : Icc (-ε) ε ∈ 𝓝 t :=
    Icc_mem_nhds htε.1 htε.2
  have hflow_at :
      HasDerivAt (α (extChartAt I x₀ x₀, v))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v) t)) t :=
    (hαder v hv t htε_closed).hasDerivAt hIccε_nhds
  have hpos :
      HasDerivAt
        (fun r : ℝ => (α (extChartAt I x₀ x₀, v) r).1)
        (α (extChartAt I x₀ x₀, v) t).2 t := by
    have hfst := hflow_at.hasFDerivAt.fst.hasDerivAt
    simpa [geodesicFlowField] using hfst
  have hshift : HasDerivAt (fun s : ℝ => t + s * c) c 0 := by
    simpa using (hasDerivAt_mul_const (x := (0 : ℝ)) c).const_add t
  have hpos_shift :
      HasDerivAt
        (fun s : ℝ => (α (extChartAt I x₀ x₀, v) (t + s * c)).1)
        (c • (α (extChartAt I x₀ x₀, v) t).2) 0 := by
    have hcomp :=
      HasDerivAt.scomp_of_eq (hg := hpos) (hh := hshift) (hy := by ring)
    simpa [Function.comp_def] using hcomp
  have hshift_tendsto :
      Tendsto (fun s : ℝ => t + s * c) (𝓝 (0 : ℝ)) (𝓝 t) := by
    simpa using hshift.continuousAt.tendsto
  have hIccτ_nhds : Icc (0 : ℝ) τ ∈ 𝓝 t :=
    Icc_mem_nhds htτ.1 htτ.2
  have hEq :
      (fun s : ℝ =>
        extChartAt I x₀
          (GeodesicTransport.expAt g x₀ ((t + s * c) • v)))
        =ᶠ[𝓝 (0 : ℝ)]
      fun s : ℝ => (α (extChartAt I x₀ x₀, v) (t + s * c)).1 := by
    filter_upwards
      [hshift_tendsto.eventually hIccτ_nhds,
       hshift_tendsto.eventually hIccε_nhds] with s hsτ hsε
    have hexps := hexp v hv (t + s * c) hsτ
    have htarget := hαtarget v hv (t + s * c) hsε
    rw [hexps]
    exact (extChartAt I x₀).right_inv htarget
  exact hpos_shift.congr_of_eventuallyEq hEq

/--
Transverse endpoint derivative with the homogeneity division made explicit.

The existing Jacobi bridge differentiates
`s ↦ expAt (t • (v + s • w))` and returns `sin t • w`.  This endpoint form
rewrites an actual endpoint perturbation `η` as `t • (t⁻¹ • η)`, giving the
factor `(sin t) / t`.
-/
theorem expAt_chart_transverse_endpoint_hasDerivAt_eq_sin_div_smul
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ τ : ℝ} {a : ℝ≥0}
    {α : E × E → ℝ → E × E}
    {v η : E} {Ψ : ℝ → E × E} {t : ℝ}
    (ht_ne : t ≠ 0)
    (hτ : 0 < τ) (hv : ‖v‖ < δ)
    (hα0 : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) r))
        (Icc (-τ) τ) r)
    (hαmem : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      α (extChartAt I x₀ x₀, v₀) r ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) a)
    (hαtarget : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      (α (extChartAt I x₀ x₀, v₀) r).1 ∈ (extChartAt I x₀).target)
    (hexp : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (0 : ℝ) τ,
      GeodesicTransport.expAt g x₀ (r • v₀) =
        (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) r).1)
    (hΨ0 : Ψ 0 = ((0 : E), t⁻¹ • η))
    (hΨlin : ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) r (Ψ r))
        (Icc (-τ) τ) r)
    {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {A R L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E × E => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E), t⁻¹ • η) A R L K)
    (hΨharmonic : ∀ r ∈ Icc tmin tmax,
      HasDerivWithinAt Ψ (harmonicJacobiOperator (Ψ r)) (Icc tmin tmax) r)
    (hΨmem : ∀ r ∈ Icc tmin tmax, Ψ r ∈ closedBall ((0 : E), t⁻¹ • η) A)
    (hsinmem : ∀ r ∈ Icc tmin tmax,
      jacobiSinState (t⁻¹ • η) r ∈ closedBall ((0 : E), t⁻¹ • η) A)
    (ht : t ∈ Icc (0 : ℝ) τ) (htJacobi : t ∈ Icc tmin tmax) :
    HasDerivAt
      (fun s : ℝ =>
        extChartAt I x₀
          (GeodesicTransport.expAt g x₀ (t • v + s • η)))
      ((Real.sin t / t) • η) 0 := by
  have hder :=
    CartanIsometry.expAt_chart_initialVelocity_hasDerivAt_eq_sin_smul
      (g := g) (x₀ := x₀) (δ := δ) (τ := τ) (a := a)
      (α := α) (v := v) (w := t⁻¹ • η) (Ψ := Ψ) (t := t)
      hτ hv hα0 hαder hαmem hαtarget hexp hΨ0 hΨlin
      hzero hpl hΨharmonic hΨmem hsinmem ht htJacobi
  convert hder using 1
  · ext s
    have harg : t • v + s • η = t • (v + s • (t⁻¹ • η)) := by
      rw [smul_add, smul_smul, smul_smul]
      congr 1
      field_simp [ht_ne]
    rw [harg]
  · simp [div_eq_mul_inv, smul_smul, mul_comm]

/--
Endpoint transverse derivative plus the Gauss cross-pairing against the radial
geodesic velocity.  The derivative vector is the same `sin t • w` vector that
appears in the zero pairing.
-/
theorem expAt_chart_transverse_hasDerivAt_and_radial_pair_eq_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ τ : ℝ} {a₀ : ℝ≥0}
    {α : E × E → ℝ → E × E}
    {v w : E} {Ψ : ℝ → E × E} {t : ℝ}
    (hτ : 0 < τ) (hv : ‖v‖ < δ)
    (hα0 : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) r))
        (Icc (-τ) τ) r)
    (hαmem : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      α (extChartAt I x₀ x₀, v₀) r ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) a₀)
    (hαtarget : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      (α (extChartAt I x₀ x₀, v₀) r).1 ∈ (extChartAt I x₀).target)
    (hexp : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (0 : ℝ) τ,
      GeodesicTransport.expAt g x₀ (r • v₀) =
        (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) r).1)
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (hΨlin : ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) r (Ψ r))
        (Icc (-τ) τ) r)
    {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {A R L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E × E => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩ ((0 : E), w) A R L K)
    (hΨharmonic : ∀ r ∈ Icc tmin tmax,
      HasDerivWithinAt Ψ (harmonicJacobiOperator (Ψ r)) (Icc tmin tmax) r)
    (hΨmem : ∀ r ∈ Icc tmin tmax, Ψ r ∈ closedBall ((0 : E), w) A)
    (hsinmem : ∀ r ∈ Icc tmin tmax, jacobiSinState w r ∈ closedBall ((0 : E), w) A)
    {bmin bmax : ℝ}
    (hbase : ∀ r ∈ Ioo bmin bmax,
      HasDerivAt (α (extChartAt I x₀ x₀, v))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v) r)) r)
    (hΨ : ∀ r ∈ Ioo bmin bmax,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) r (Ψ r)) r)
    (hflow : ∀ r ∈ Ioo bmin bmax,
      HasDerivAt
        (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) r) (Ψ r) 0)
    (hspeed_const : ∀ r ∈ Ioo bmin bmax,
      (fun s : ℝ =>
        GeodesicTransport.chartGeodesicMetric g x₀
          (α (extChartAt I x₀ x₀, v + s • w) r).1
          (α (extChartAt I x₀ x₀, v + s • w) r).2
          (α (extChartAt I x₀ x₀, v + s • w) r).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
          (v + s • w) (v + s • w)))
    (hGd_base : ∀ r ∈ Ioo bmin bmax,
      DifferentiableAt ℝ (GeodesicTransport.chartGeodesicMetric g x₀)
        (α (extChartAt I x₀ x₀, v) r).1)
    (hGd_initial :
      DifferentiableAt ℝ (GeodesicTransport.chartGeodesicMetric g x₀) (extChartAt I x₀ x₀))
    (hbzero : (0 : ℝ) ∈ Ioo bmin bmax)
    (horth : GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v w = 0)
    (hcut : GeodesicTransport.cutoff (n := 3) x₀
      (α (extChartAt I x₀ x₀, v) t).1 = 1)
    (ht : t ∈ Icc (0 : ℝ) τ)
    (htJacobi : t ∈ Icc tmin tmax)
    (htGauss : t ∈ Ioo bmin bmax) :
    HasDerivAt
        (fun s : ℝ =>
          extChartAt I x₀
            (GeodesicTransport.expAt g x₀ (t • (v + s • w))))
        (Real.sin t • w) 0 ∧
      CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I x₀ x₀, v) t).1
        (Real.sin t • w)
        (α (extChartAt I x₀ x₀, v) t).2 = 0 := by
  have hder :=
    CartanIsometry.expAt_chart_initialVelocity_hasDerivAt_eq_sin_smul
      (g := g) (x₀ := x₀) (δ := δ) (τ := τ) (a := a₀)
      (α := α) (v := v) (w := w) (Ψ := Ψ) (t := t)
      hτ hv hα0 hαder hαmem hαtarget hexp hΨ0 hΨlin
      hzero hpl hΨharmonic hΨmem hsinmem ht htJacobi
  have hsin : (Ψ t).1 = Real.sin t • w :=
    jacobi_position_eq_sin_smul_on_Icc
      (w := w) hzero (hpl := hpl) (Ψ := Ψ)
      hΨharmonic hΨmem hsinmem hΨ0 htJacobi
  have hgauss :
      CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I x₀ x₀, v) t).1
        (Ψ t).1
        (α (extChartAt I x₀ x₀, v) t).2 = 0 :=
    GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_orthogonal_chartMetric
      (g := g) (x₀ := x₀) (α := α) (z₀ := extChartAt I x₀ x₀)
      (v := v) (w := w) (Ψ := Ψ) (a := bmin) (b := bmax) (t := t)
      hbase hΨ hflow hspeed_const hGd_base hGd_initial
      (hα0 v hv) hΨ0 hbzero horth hcut htGauss
  exact ⟨hder, by simpa [hsin] using hgauss⟩

end Endpoint

section ChainRule

universe u

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- Chart-coordinate Cartan composition `expAt p₀ ∘ L ∘ (expAt x₀)⁻¹`. -/
def cartanChartMap
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) : E → E :=
  fun y : E =>
    GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := roundSphereMetric3) p₀
      (L ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x₀).symm y))

/--
Strict chain rule for the chart-coordinate Cartan composition at an arbitrary
source exponential coordinate where both endpoint exponential differentials are
available as strict derivatives.
-/
theorem cartanChartMap_hasStrictFDerivAt_of_expAtChart
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsource :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htarget :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v)) :
    HasStrictFDerivAt
      (cartanChartMap g x₀ p₀ L)
      ((B : E →L[ℝ] E).comp
        ((L.toContinuousLinearEquiv : E →L[ℝ] E).comp
          (A.symm : E →L[ℝ] E)))
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀
  have hleft : eM.symm (eM v) = v := eM.left_inv hvsrc
  have hsource' : HasStrictFDerivAt eM (A : E →L[ℝ] E) (eM.symm (eM v)) := by
    rw [hleft]
    exact hsource
  have hinv :
      HasStrictFDerivAt eM.symm (A.symm : E →L[ℝ] E) (eM v) :=
    eM.hasStrictFDerivAt_symm (eM.map_source hvsrc) hsource'
  have hL :
      HasStrictFDerivAt (fun z : E => L z)
        (L.toContinuousLinearEquiv : E →L[ℝ] E) v :=
    L.toContinuousLinearEquiv.hasStrictFDerivAt
  have hL_at :
      HasStrictFDerivAt (fun z : E => L z)
        (L.toContinuousLinearEquiv : E →L[ℝ] E) (eM.symm (eM v)) := by
    rw [hleft]
    exact hL
  have hL' :
      HasStrictFDerivAt (fun y : E => L (eM.symm y))
        ((L.toContinuousLinearEquiv : E →L[ℝ] E).comp
          (A.symm : E →L[ℝ] E)) (eM v) := by
    simpa [Function.comp_def] using hL_at.comp (eM v) hinv
  have htarget' :
      HasStrictFDerivAt eS (B : E →L[ℝ] E) (L (eM.symm (eM v))) := by
    rw [hleft]
    exact htarget
  have hcomp := htarget'.comp (eM v) hL'
  simpa [cartanChartMap, eM, eS, Function.comp_def] using hcomp

/--
At the anchor, the strict chain rule reduces to the tangent alignment `L`:
both exponential chart maps have strict derivative `id` at zero and the source
inverse has derivative `id`.
-/
theorem cartanChartMap_hasStrictFDerivAt_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    HasStrictFDerivAt
      (cartanChartMap g x₀ p₀ L)
      (L.toContinuousLinearEquiv : E →L[ℝ] E)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) (0 : E)) := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀
  have hvsrc : (0 : E) ∈ eM.source :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) x₀
  have hsource :
      HasStrictFDerivAt eM
        ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E)
        (0 : E) := by
    simpa [eM] using
      GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
        (g := g) (x₀ := x₀)
  have htarget :
      HasStrictFDerivAt eS
        ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E)
        (L (0 : E)) := by
    simpa [eS] using
      GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
        (g := roundSphereMetric3) (x₀ := p₀)
  have h :=
    cartanChartMap_hasStrictFDerivAt_of_expAtChart
      (g := g) (x₀ := x₀) (p₀ := p₀) (L := L)
      (v := (0 : E))
      (A := ContinuousLinearEquiv.refl ℝ E)
      (B := ContinuousLinearEquiv.refl ℝ E)
      hvsrc hsource htarget
  simpa using h

end ChainRule

section PullbackAlgebra

variable {M : Type*}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Final radial/transverse algebra for the pullback identity.  If an endpoint
differential is read as the same radial scale `ρ` and transverse scale `σ` on
the source side, then applying the tangent alignment preserves the paired
metric value exactly.
-/
theorem tangentAlignment_scaled_radial_transverse_pair
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (ρ σ : ℝ) (v u u' : E) :
    CartanMap.targetAnchorChartMetric p₀
      (ρ • L (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) +
        σ • L (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u))
      (ρ • L (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x₀) v u') +
        σ • L (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u')) =
    CartanMap.sourceAnchorChartMetric g x₀
      (ρ • CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x₀) v u +
        σ • CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u)
      (ρ • CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x₀) v u' +
        σ • CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u') := by
  simp [map_add, CartanMap.TangentAlignment.map_app]

end PullbackAlgebra

end CartanDifferential
end Poincare
