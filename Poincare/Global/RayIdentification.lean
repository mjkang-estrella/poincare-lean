import Poincare.Global.CartanDifferential
import Poincare.Global.CorrectedRadial

/-!
# Ray identification for radial linearized endpoints

This module identifies the radial initial-velocity linearized endpoint with
the derivative of the geodesic ray.  The proof compares two already-exported
fixed-time derivative computations for the same charted endpoint curve:

* `CartanIsometry.expAt_chart_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`
  gives the linearized value `(Ψ T).1`;
* `CartanDifferential.expAt_chart_radial_hasDerivAt_of_uniform_geodesicFlow`
  gives the ray derivative `T • γ'(T)`.

Uniqueness of derivatives then identifies the two values.
-/

noncomputable section

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace RayIdentification

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/--
The radial linearized endpoint is the ray derivative.

For a uniform PL chart geodesic flow `α`, if `Ψ` is the linearized solution
along the base velocity `v` with initial state `(0, v)`, then at time `T` its
position component is exactly `T` times the chart velocity of the base geodesic.
-/
theorem radial_linearized_endpoint_eq_time_smul_velocity_of_uniform_geodesicFlow
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ τ : ℝ} {a : ℝ≥0}
    {α : E × E → ℝ → E × E}
    {v : E} {Ψ : ℝ → E × E} {T : ℝ}
    (hτ : 0 < τ) (hv : ‖v‖ < δ)
    (hα0 : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) r))
        (Icc (-τ) τ) r)
    (hαmem : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      α (extChartAt I x₀ x₀, v₀) r ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) a)
    (hαtarget : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      (α (extChartAt I x₀ x₀, v₀) r).1 ∈ (extChartAt I x₀).target)
    (hexp : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (0 : ℝ) τ,
      expAt g x₀ (r • v₀) =
        (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) r).1)
    (hΨ0 : Ψ 0 = ((0 : E), v))
    (hΨlin : ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) r (Ψ r))
        (Icc (-τ) τ) r)
    (hT : T ∈ Ioo (0 : ℝ) τ) :
    (Ψ T).1 = T • (α (extChartAt I x₀ x₀, v) T).2 := by
  have hTcc : T ∈ Icc (0 : ℝ) τ :=
    ⟨le_of_lt hT.1, le_of_lt hT.2⟩
  have hTfull : T ∈ Ioo (-τ) τ := by
    constructor
    · linarith [hτ, hT.1]
    · exact hT.2
  have hlinear :
      HasDerivAt
        (fun s : ℝ =>
          extChartAt I x₀
            (expAt g x₀ (T • (v + s • v))))
        (Ψ T).1 0 :=
    CartanIsometry.expAt_chart_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (τ := τ) (a := a)
      (α := α) (v := v) (w := v) (Ψ := Ψ) (t := T)
      hτ hv hα0 hαder hαmem hαtarget hexp hΨ0 hΨlin hTcc
  have hray :
      HasDerivAt
        (fun s : ℝ =>
          extChartAt I x₀
            (expAt g x₀ ((T + s * T) • v)))
        (T • (α (extChartAt I x₀ x₀, v) T).2) 0 :=
    CartanDifferential.expAt_chart_radial_hasDerivAt_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (τ := τ) (ε := τ)
      (α := α) (v := v) (t := T) (c := T)
      hv hαder hαtarget hexp hT hTfull
  have hsame :
      (fun s : ℝ =>
          extChartAt I x₀
            (expAt g x₀ (T • (v + s • v)))) =
        fun s : ℝ =>
          extChartAt I x₀
            (expAt g x₀ ((T + s * T) • v)) := by
    funext s
    congr 2
    module
  rw [hsame] at hlinear
  exact hlinear.unique hray

/--
Endpoint pairing consequence of the ray identification: once the endpoint
velocity has squared speed `speed ^ 2`, the radial linearized endpoint has
the plain ray scale `T ^ 2 * speed ^ 2`.
-/
theorem radial_endpoint_pairing_eq_plainRadialScale
    (G : E →L[ℝ] E →L[ℝ] ℝ)
    {Ψ : ℝ → E × E} {V : E} {T speed : ℝ}
    (hRay : (Ψ T).1 = T • V)
    (hspeed : G V V = speed ^ 2) :
    G (Ψ T).1 (Ψ T).1 = CorrectedRadial.plainRadialScale speed T := by
  calc
    G (Ψ T).1 (Ψ T).1 = G (T • V) (T • V) := by rw [hRay]
    _ = CorrectedRadial.plainRadialScale speed T := by
      simp [CorrectedRadial.plainRadialScale, hspeed, pow_two, mul_assoc]

/--
Linearity turns the ray identification for `v` into the corresponding radial
line pairing for any two scalar multiples of `v`.
-/
theorem radial_line_endpoint_pairing_eq_coeff_mul_plainRadialScale
    (G : E →L[ℝ] E →L[ℝ] ℝ)
    {Ψ : E → ℝ → E × E} {v V : E} {T speed : ℝ}
    (hRay : (Ψ v T).1 = T • V)
    (hsmul : ∀ (c : ℝ) (w : E), (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed : G V V = speed ^ 2) (c c' : ℝ) :
    G ((Ψ (c • v) T).1) ((Ψ (c' • v) T).1) =
      (c * c') * CorrectedRadial.plainRadialScale speed T := by
  calc
    G ((Ψ (c • v) T).1) ((Ψ (c' • v) T).1) =
        G (c • (Ψ v T).1) (c' • (Ψ v T).1) := by
          rw [hsmul c v, hsmul c' v]
    _ = (c * c') * CorrectedRadial.plainRadialScale speed T := by
      simp [hRay, hspeed, CorrectedRadial.plainRadialScale, pow_two,
        mul_left_comm, mul_comm]

/--
The same radial-line pairing, written with the project radial projection API.
-/
theorem radialPart_endpoint_pairing_eq_radialCoeff_mul_plainRadialScale
    (G B : E →L[ℝ] E →L[ℝ] ℝ)
    {Ψ : E → ℝ → E × E} {v V : E} {T speed : ℝ}
    (hRay : (Ψ v T).1 = T • V)
    (hsmul : ∀ (c : ℝ) (w : E), (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed : G V V = speed ^ 2) (u u' : E) :
    G ((Ψ (CartanPullback.radialPart B v u) T).1)
      ((Ψ (CartanPullback.radialPart B v u') T).1) =
        (CartanPullback.radialCoeff B v u *
            CartanPullback.radialCoeff B v u') *
          CorrectedRadial.plainRadialScale speed T := by
  simpa [CartanPullback.radialPart] using
    radial_line_endpoint_pairing_eq_coeff_mul_plainRadialScale
      (G := G) (Ψ := Ψ) (v := v) (V := V) (T := T) (speed := speed)
      hRay hsmul hspeed
      (CartanPullback.radialCoeff B v u)
      (CartanPullback.radialCoeff B v u')

end RayIdentification
end Poincare
