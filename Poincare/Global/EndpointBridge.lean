import Poincare.Global.FTransitionDone

/-!
# Endpoint derivative bridge for the Cartan F-transition law

This module removes the artificial open-neighborhood endpoint-field hypothesis
from `FTransitionDone`: a `C²` Cartan chart map already supplies the canonical
endpoint field `q ↦ fderiv ℝ F q`, its derivative at the endpoint, and the
open agreement on `Set.univ`.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace EndpointBridge

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
`ContDiffAt ℝ 2` supplies the canonical endpoint field demanded by
`FTransitionDone`, so the signed F-transition law only needs the remaining
pointwise `C²` and metric-derivative hypotheses.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_contDiffAt_two
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
          ContDiffAt ℝ 2 F (eM v) →
          HasFDerivAt G₀ (fderiv ℝ G₀ (eM v)) (eM v) →
          HasFDerivAt G₁ (fderiv ℝ G₁ (F (eM v))) (F (eM v)) →
          ∀ (b₀ b₁ : LinearMap.BilinForm ℝ E3)
            (hb₀ : b₀.Nondegenerate) (hb₁ : b₁.Nondegenerate),
            (∀ a b : E3, b₀ a b = G₀ (eM v) a b) →
            (∀ a b : E3, b₁ a b = G₁ (F (eM v)) a b) →
            ∀ u w : E3,
              CovariantDerivative.christoffelAt G₁ (F (eM v)) b₁
                  hb₁ (DF v w) (DF v u) =
                DF v
                    (CovariantDerivative.christoffelAt G₀ (eM v) b₀
                      hb₀ w u) -
                  ((fderiv ℝ (fun q : E3 => fderiv ℝ F q) (eM v)) u) w := by
  rcases
      Poincare.FTransitionDone.exists_cartanChartMap_christoffelAt_F_transition_law_of_endpoint_hasFDerivAt_on_open
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ_pos, Afield, Bfield, DF, hDF_def, htransition⟩
  use ρ, hρ_pos, Afield, Bfield, DF
  constructor
  · exact hDF_def
  intro v hv hvne
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let F := CartanDifferential.cartanChartMap g x₀ p₀ L
  let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric g.inner x₀ z
  let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
  intro hvsrc hC2 hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
  have hendpoint :
      HasFDerivAt (fun q : E3 => fderiv ℝ F q)
        (fderiv ℝ (fun q : E3 => fderiv ℝ F q) (eM v)) (eM v) := by
    have hC1 : ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ F q) (eM v) := by
      exact hC2.fderiv_right (m := 1) (by norm_num)
    exact (hC1.differentiableAt (by norm_num)).hasFDerivAt
  exact
    htransition v hv hvne hvsrc
      (fun q : E3 => fderiv ℝ F q)
      (fderiv ℝ (fun q : E3 => fderiv ℝ F q) (eM v))
      Set.univ isOpen_univ (Set.mem_univ (eM v)) (by intro q _hq; rfl)
      hendpoint hC2 hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w

end EndpointBridge
end Poincare
