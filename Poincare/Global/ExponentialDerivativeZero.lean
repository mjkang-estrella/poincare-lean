import Poincare.Global.ExponentialRayLaw
import Poincare.Global.GaussLemmaIntegrated

/-!
# Derivative of the fixed-time exponential at the zero velocity

This module records the verified zero-velocity derivative facts currently
available from the fixed-time exponential package.

The short-time Jacobi expansion is stated both as a derivative and as the
equivalent first-order little-o remainder for the position component.  The
exponential derivative is proved in the scalar ray variable for every chart
direction, by scaling the existing small-direction right derivative and then
combining the right and left half-neighborhoods.

The final Fréchet statement is isolated as a remainder criterion: a uniform
little-o estimate in the velocity variable immediately gives derivative
`1 : E →L[ℝ] E`.  The uniform estimate itself is not asserted here.
-/

noncomputable section

open Asymptotics Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-!
## Jacobi short-time expansion
-/

/--
For a chart linearized geodesic solution with initial data `Ψ 0 = (0, w)`,
the position component has derivative `w` at time `0`.

This is the fundamental-theorem-style short-time expansion `J t = t • w +
o(t)`: the linearized equation gives `J' = K`, and the initial condition gives
`K 0 = w`.
-/
theorem chart_linearized_position_hasDerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε : ℝ} {γ Ψ : ℝ → E × E} {w : E}
    (hε : 0 < ε)
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (hΨder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ t (Ψ t))
        (Icc (-ε) ε) t) :
    HasDerivAt (fun t : ℝ => (Ψ t).1) w 0 := by
  have h0mem : (0 : ℝ) ∈ Icc (-ε) ε := by
    constructor <;> linarith
  have hIcc : Icc (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hε
  have hΨat :
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ 0 (Ψ 0)) 0 :=
    (hΨder 0 h0mem).hasDerivAt hIcc
  have hpos :=
    chart_linearized_fst_hasDerivAt
      (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := 0) hΨat
  simpa [hΨ0] using hpos

/--
Little-o form of `chart_linearized_position_hasDerivAt_zero`:
`J t - t • w = o(t)` at the origin.
-/
theorem chart_linearized_position_sub_linear_isLittleO_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε : ℝ} {γ Ψ : ℝ → E × E} {w : E}
    (hε : 0 < ε)
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (hΨder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ t (Ψ t))
        (Icc (-ε) ε) t) :
    (fun t : ℝ => (Ψ t).1 - t • w) =o[𝓝 (0 : ℝ)] (fun t : ℝ => t) := by
  have hder :=
    chart_linearized_position_hasDerivAt_zero
      (g := g) (x₀ := x₀) hε hΨ0 hΨder
  simpa [hΨ0] using hder.isLittleO

/-!
## Ray derivative of `expAt` at zero
-/

/--
The charted fixed-time exponential has the right scalar derivative `w` at the
zero velocity in every direction `w`.

The exported ray law gives this directly for sufficiently small directions.
For an arbitrary `w`, scale it into that small ball and compose the ray
parameter with a positive scalar.
-/
theorem expAt_chart_hasDerivWithinAt_zero_smul_Ici
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (w : E) :
    HasDerivWithinAt
      (fun s : ℝ => extChartAt I x₀ (expAt g x₀ (s • w)))
      w (Ici (0 : ℝ)) 0 := by
  rcases expAt_chart_hasDerivWithinAt_of_norm_lt
      (g := g) (x₀ := x₀) with
    ⟨_τ, _hτ, δ, hδ, hray⟩
  let c : ℝ := ‖w‖ / δ + 1
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  let v : E := c⁻¹ • w
  have hv : ‖v‖ < δ := by
    have hlt : ‖w‖ < δ * c := by
      dsimp [c]
      field_simp [ne_of_gt hδ]
      linarith [norm_nonneg w, hδ]
    change ‖c⁻¹ • w‖ < δ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc_pos)]
    calc
      c⁻¹ * ‖w‖ < c⁻¹ * (δ * c) :=
        mul_lt_mul_of_pos_left hlt (inv_pos.mpr hc_pos)
      _ = δ := by field_simp [hc_ne]
  have hsmall :
      HasDerivWithinAt
        (fun t : ℝ => extChartAt I x₀ (expAt g x₀ (t • v)))
        v (Ici (0 : ℝ)) 0 :=
    hray v hv
  have hscale :
      HasDerivWithinAt (fun s : ℝ => c * s) c (Ici (0 : ℝ)) 0 :=
    (hasDerivAt_const_mul (x := (0 : ℝ)) c).hasDerivWithinAt
  have hmaps :
      MapsTo (fun s : ℝ => c * s) (Ici (0 : ℝ)) (Ici (0 : ℝ)) := by
    intro s hs
    exact mul_nonneg hc_pos.le hs
  have hcomp :=
    hsmall.scomp_of_eq (0 : ℝ) hscale hmaps (by simp)
  convert hcomp using 1
  · funext s
    change extChartAt I x₀ (expAt g x₀ (s • w)) =
      extChartAt I x₀ (expAt g x₀ ((c * s) • v))
    rw [show (c * s) • v = s • w from by
      calc
        (c * s) • v = ((c * s) * c⁻¹) • w := by
          simp [v, smul_smul]
        _ = s • w := by
          congr 1
          field_simp [hc_ne]]
  · simp [v, smul_smul, hc_ne]

/--
The charted fixed-time exponential has two-sided scalar derivative `w` at the
zero velocity in every direction `w`.
-/
theorem expAt_chart_hasDerivAt_zero_smul
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (w : E) :
    HasDerivAt
      (fun s : ℝ => extChartAt I x₀ (expAt g x₀ (s • w))) w 0 := by
  have hright :=
    expAt_chart_hasDerivWithinAt_zero_smul_Ici
      (g := g) (x₀ := x₀) w
  have hneg :=
    expAt_chart_hasDerivWithinAt_zero_smul_Ici
      (g := g) (x₀ := x₀) (-w)
  have hneg_scale :
      HasDerivWithinAt (fun s : ℝ => -s) (-1 : ℝ) (Iic (0 : ℝ)) 0 :=
    (hasDerivAt_neg (x := (0 : ℝ))).hasDerivWithinAt
  have hneg_maps :
      MapsTo (fun s : ℝ => -s) (Iic (0 : ℝ)) (Ici (0 : ℝ)) := by
    intro s hs
    have hsle : s ≤ 0 := by simpa using hs
    exact neg_nonneg.mpr hsle
  have hleft_comp :=
    hneg.scomp_of_eq (0 : ℝ) hneg_scale hneg_maps (by simp)
  have hleft :
      HasDerivWithinAt
        (fun s : ℝ => extChartAt I x₀ (expAt g x₀ (s • w)))
        w (Iic (0 : ℝ)) 0 := by
    convert hleft_comp using 1
    · ext s
      simp [neg_smul, smul_neg]
    · simp
  have hboth := hleft.union hright
  have huniv : Iic (0 : ℝ) ∪ Ici (0 : ℝ) = univ := by
    ext s
    constructor
    · intro _; trivial
    · intro _
      by_cases hs : s ≤ 0
      · exact Or.inl hs
      · exact Or.inr (le_of_not_ge hs)
  have hnhds : Iic (0 : ℝ) ∪ Ici (0 : ℝ) ∈ 𝓝 (0 : ℝ) := by
    simp [huniv]
  exact hboth.hasDerivAt hnhds

/-- The fixed-time exponential is continuous at the zero velocity. -/
theorem expAt_continuousAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ContinuousAt (expAt g x₀) (0 : E) := by
  rcases expAt_continuousOn_smallBall (g := g) (x₀ := x₀) with
    ⟨ρ, hρ, hcont⟩
  exact hcont.continuousAt (Metric.ball_mem_nhds (0 : E) hρ)

/-- The chart representation of `expAt` is continuous at the zero velocity. -/
theorem expAt_chart_continuousAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ContinuousAt
      (fun v : E => extChartAt I x₀ (expAt g x₀ v)) (0 : E) := by
  have h_exp := expAt_continuousAt_zero (g := g) (x₀ := x₀)
  have h_chart : ContinuousAt (extChartAt I x₀) x₀ :=
    continuousAt_extChartAt x₀
  simpa [Function.comp_def] using
    h_chart.comp_of_eq h_exp (by simp [expAt_zero])

/-!
## Fréchet derivative criterion
-/

/--
Uniform velocity-variable little-o criterion for the desired Fréchet
derivative at zero.  This is the exact upgrade needed beyond the directional
and continuity results above.
-/
theorem expAt_chart_hasFDerivAt_zero_of_remainder
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (hrem :
      (fun v : E =>
        extChartAt I x₀ (expAt g x₀ v) - (extChartAt I x₀ x₀ + v))
          =o[𝓝 (0 : E)] (fun v : E => v)) :
    HasFDerivAt
      (fun v : E => extChartAt I x₀ (expAt g x₀ v))
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
  rw [hasFDerivAt_iff_isLittleO]
  simpa [expAt_zero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrem

end GeodesicTransport
end Poincare
