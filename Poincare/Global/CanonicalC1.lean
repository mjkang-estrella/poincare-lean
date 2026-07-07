import Poincare.Global.LevelThreeFeed

/-!
# Canonical C1 feed into the produced-field tower

This module isolates the last verified consumer step after canonical
`q ↦ fderiv ℝ e q` regularity has been obtained for the two exponential
charts.  The canonical `C1` facts identify the produced derivative fields with
the canonical fields near the base points via `LevelThreeFeed`; the selected
field regularity then feeds the existing `TowerCloses` F-transition consumer.
-/

noncomputable section

open Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CanonicalC1

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Canonical `C1` regularity of the two exponential-chart Frechet derivative
fields supplies the selected-field `C1` inputs demanded by the produced-field
F-transition tower.

The statement keeps the actual produced `sourceD` and `targetD` fields and
their local derivative facts visible, but the final transition-law consumer now
asks for `ContDiffAt ℝ 1 (fun q => fderiv ℝ e q)` on the canonical source and
target exponential charts instead of `ContDiffAt` for the noncomputably
selected fields.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_canonical_fderiv_c1
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) (L : CartanMap.TangentAlignment g x0 p0) :
    ∃ ρ > (0 : ℝ),
      ∃ sourceD targetD : E3 → E3 →L[ℝ] E3,
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
          v ∈ eM.source ∧
            L v ∈ eS.source ∧
            HasFDerivAt eM (sourceD v) v ∧
            HasFDerivAt eS (targetD (L v)) (L v) ∧
            (∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q) ∧
            (∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q) ∧
            (ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eM q) v →
              ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eS q) (L v) →
              ∀ {sourceIso : E3 ≃L[ℝ] E3},
                HasFDerivAt eM (sourceIso : E3 →L[ℝ] E3) v →
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
                        ((fderiv ℝ (fun q : E3 => fderiv ℝ F q) (eM v)) u) w) := by
  rcases
      TowerCloses.exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_derivative_fields_c1
        (g := g) hcurv (x0 := x0) (p0 := p0) L with
    ⟨ρ, hρ_pos, sourceD, targetD, Afield, Bfield, DF, hDF_def, htransition⟩
  use ρ, hρ_pos, sourceD, targetD, Afield, Bfield, DF
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
  rcases htransition v hv hvne with
    ⟨hvsrc, hvtgt, hsource_at, htarget_at, hsource_near, htarget_near,
      hconsume⟩
  exact
    ⟨hvsrc, hvtgt, hsource_at, htarget_at, hsource_near, htarget_near, by
      intro hsource_fderiv_c1 htarget_fderiv_c1 sourceIso hsourceIso_deriv hG₀ hG₁
        b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
      have hselected_c1 :
          ContDiffAt ℝ 1 sourceD v ∧ ContDiffAt ℝ 1 targetD (L v) :=
        LevelThreeFeed.selected_expChart_derivative_fields_contDiffAt_one_of_fderiv_contDiffAt_one
          (eM := eM) (eS := eS) (sourceD := sourceD) (targetD := targetD)
          (v := v) (w := L v)
          hsource_near hsource_fderiv_c1 htarget_near htarget_fderiv_c1
      exact
        hconsume (sourceIso := sourceIso) hselected_c1.1 hsourceIso_deriv
          hselected_c1.2 hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w⟩

end CanonicalC1
end Poincare
