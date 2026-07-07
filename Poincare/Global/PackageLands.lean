import Poincare.Global.EndpointBridge
import Poincare.Global.ExpChartC2

/-!
# Neighborhood derivative-field package feed

This module composes the already exported chart-side derivative-field handoff
with the endpoint bridge for the Cartan F-transition law.  The remaining input
is exactly the non-hypothetical production of the two exponential-chart
derivative fields and their `C1` dependence.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace PackageLands

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The exponential-chart neighborhood derivative-field package is enough to feed
the `C2` Cartan-map bridge and hence the endpoint F-transition assembly.

This removes the separate `ContDiffAt ℝ 2 F (eM v)` hypothesis from the
transition-law consumer; the only remaining chart-side regularity inputs are
the two derivative fields, their neighborhood `HasFDerivAt` facts, the source
invertible derivative, and their `C1` dependence.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_expChart_derivative_fields
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) (L : CartanMap.TangentAlignment g x0 p0) :
    ∃ ρ > (0 : ℝ),
      ∃ Afield Bfield : E3 → E3 ≃L[ℝ] E3,
      ∃ DF : E3 → E3 →L[ℝ] E3,
        (∀ v : E3,
          DF v =
            CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)) ∧
        ∀ v : E3, ‖v‖ < ρ → v ≠ 0 →
          let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0
          let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0
          let F := CartanDifferential.cartanChartMap g x0 p0 L
          let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric g.inner x0 z
          let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p0 z
          v ∈ eM.source →
          ∀ {sourceD targetD : E3 → E3 →L[ℝ] E3}
            {sourceIso : E3 ≃L[ℝ] E3},
            (∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q) →
            ContDiffAt ℝ 1 sourceD v →
            HasFDerivAt eM (sourceIso : E3 →L[ℝ] E3) v →
            (∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q) →
            ContDiffAt ℝ 1 targetD (L v) →
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
      EndpointBridge.exists_cartanChartMap_christoffelAt_F_transition_law_of_contDiffAt_two
        (g := g) hcurv (x₀ := x0) (p₀ := p0) L with
    ⟨ρ, hρ_pos, Afield, Bfield, DF, hDF_def, htransition⟩
  use ρ, hρ_pos, Afield, Bfield, DF
  constructor
  · exact hDF_def
  intro v hv hvne
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p0
  let F := CartanDifferential.cartanChartMap g x0 p0 L
  let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric g.inner x0 z
  let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p0 z
  intro hvsrc sourceD targetD sourceIso hsource_deriv hsourceD_c1
    hsourceIso_deriv htarget_deriv htargetD_c1 hG₀ hG₁
    b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
  have hC2 :
      ContDiffAt ℝ 2 (CartanDifferential.cartanChartMap g x0 p0 L) (eM v) :=
    ExpChartC2.cartanChartMap_contDiffAt_two_of_expChart_derivative_fields
      (g := g) (x0 := x0) (p0 := p0) (L := L) (v := v)
      (sourceD := sourceD) (targetD := targetD) (sourceIso := sourceIso)
      hvsrc hsource_deriv hsourceD_c1 hsourceIso_deriv htarget_deriv
      htargetD_c1
  exact
    htransition v hv hvne hvsrc hC2 hG₀ hG₁
      b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w

end PackageLands
end Poincare
