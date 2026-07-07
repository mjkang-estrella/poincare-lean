import Poincare.Global.DifferentialField
import Poincare.Global.LCNaturality

/-!
# Cartan-map F-transition law, reduced to the remaining germ regularity

This module instantiates the generic Levi-Civita naturality algebra with the
Cartan chart map and the pointwise differential field from
`DifferentialField`.  The statement keeps the genuinely missing input explicit:
a chart-indexed differentiable extension of the selected normal-coordinate
field together with the eventual pullback germ around the chart point.
-/

noncomputable section

open Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace FTransition

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Strict partial F-transition law for the Cartan chart map.

The theorem consumes the nonzero normal-coordinate differential field from
`DifferentialField.exists_cartanChartDifferential_field_on_punctured_ball`.
At a point `z = exp_x(v)`, any chart-indexed derivative field `D` whose value is
that selected field, whose derivative is symmetric, and whose pullback identity
holds as an eventual germ, satisfies the signed Christoffel transport law for
the raw source and round target chart metrics.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_on_punctured_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ Afield Bfield : E3 → E3 ≃L[ℝ] E3,
      ∃ DF : E3 → E3 →L[ℝ] E3,
        (∀ v : E3,
          DF v =
            CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)) ∧
        ∀ v : E3, ‖v‖ < ρ → v ≠ 0 →
          let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
          let F := CartanDifferential.cartanChartMap g x₀ p₀ L
          let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric g.inner x₀ z
          let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
          v ∈ eM.source →
          ∀ (D : E3 → E3 →L[ℝ] E3),
            D (eM v) = DF v →
            HasFDerivAt D (fderiv ℝ D (eM v)) (eM v) →
            (∀ a b : E3,
              (fderiv ℝ D (eM v) a) b = (fderiv ℝ D (eM v) b) a) →
            (∀ a b : E3,
              (fun q : E3 => G₁ (F q) (D q a) (D q b)) =ᶠ[𝓝 (eM v)]
                (fun q : E3 => G₀ q a b)) →
            HasFDerivAt G₀ (fderiv ℝ G₀ (eM v)) (eM v) →
            HasFDerivAt G₁ (fderiv ℝ G₁ (F (eM v))) (F (eM v)) →
            ∀ (b₀ b₁ : LinearMap.BilinForm ℝ E3)
              (hb₀ : b₀.Nondegenerate) (hb₁ : b₁.Nondegenerate),
              (∀ a b : E3, b₀ a b = G₀ (eM v) a b) →
              (∀ a b : E3, b₁ a b = G₁ (F (eM v)) a b) →
              ∀ u w : E3,
                CovariantDerivative.christoffelAt G₁ (F (eM v)) b₁
                    hb₁ (D (eM v) w) (D (eM v) u) =
                  D (eM v)
                      (CovariantDerivative.christoffelAt G₀ (eM v) b₀
                        hb₀ w u) -
                    (fderiv ℝ D (eM v) u) w := by
  rcases
      DifferentialField.exists_cartanChartDifferential_field_on_punctured_ball
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ_pos, Afield, Bfield, DF, hDF_def, hfield⟩
  use ρ, hρ_pos, Afield, Bfield, DF
  constructor
  · exact hDF_def
  intro v hv hvne
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀
  let F := CartanDifferential.cartanChartMap g x₀ p₀ L
  let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric g.inner x₀ z
  let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
  intro hvsrc D hD_at hD hD2symm hpull_germ hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
  rcases hfield v hv hvne with ⟨hDFinv, hFstrict, hpullDF⟩
  have hFz : F (eM v) = eS (L v) := by
    change eS (L (eM.symm (eM v))) = eS (L v)
    rw [eM.left_inv hvsrc]
  have hDinv : (D (eM v)).IsInvertible := by
    rw [hD_at]
    exact hDFinv
  have hsigma : HasFDerivAt F (D (eM v)) (eM v) := by
    rw [hD_at]
    simpa [F, eM] using hFstrict.hasFDerivAt
  have hdiff :
      ∀ e a b : E3,
        ((fderiv ℝ G₁ (F (eM v)) (D (eM v) e)) (D (eM v) a)
            (D (eM v) b)) +
          G₁ (F (eM v)) ((fderiv ℝ D (eM v) e) a) (D (eM v) b) +
          G₁ (F (eM v)) (D (eM v) a)
            ((fderiv ℝ D (eM v) e) b) =
        ((fderiv ℝ G₀ (eM v) e) a b) :=
    GeodesicTransport.differentiated_pullback_hdiff_of_eventuallyEq
      (G0 := G₀) (G1 := G₁) (sigma := F) (D := D)
      hsigma hD hG₀ hG₁ hpull_germ
  have hpull : ∀ a b : E3,
      G₁ (F (eM v)) (D (eM v) a) (D (eM v) b) =
        G₀ (eM v) a b := by
    intro a b
    rw [hFz, hD_at]
    simpa [G₀, G₁, eM, eS] using hpullDF a b
  have hG₁symm : ∀ a b : E3,
      G₁ (F (eM v)) a b = G₁ (F (eM v)) b a := by
    intro a b
    exact
      CovariantDerivative.chartMetric_symm roundSphereMetric3.inner
        (fun z x y => roundSphereMetric3.symm z x y) p₀ (F (eM v)) a b
  exact
    GeodesicTransport.christoffelAt_map_eq_signed_transport_of_differentiated_pullback
      (G₀ := G₀) (G₁ := G₁) (F := F) (D := D) (z := eM v)
      hDinv hD2symm hdiff hpull hG₁symm b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w

end FTransition
end Poincare
