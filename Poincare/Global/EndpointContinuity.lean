import Poincare.Global.CanonicalC1

/-!
# Endpoint continuity feed for the canonical C1 assembly

This module replaces the canonical `ContDiffAt` assumptions in the final
produced-field F-transition consumer by the concrete endpoint-continuity data
expected from the third-variation endpoint family.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace EndpointContinuity

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Endpoint-continuity data for the third-variation endpoint CLM fires the
canonical `C1` bridge used by the produced-field F-transition tower.

For each punctured normal vector, the statement keeps the source and target
endpoint CLM fields explicit.  If each endpoint field is continuous on a
neighborhood and locally represents the Frechet derivative of the canonical
`q ↦ fderiv ℝ e q` field, then `CanonicalC1` supplies the selected-field `C1`
facts and the existing tower yields the signed Christoffel F-transition law.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_endpoint_continuity
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
            (∀ {sourceEndpoint targetEndpoint : E3 → E3 →L[ℝ] E3 →L[ℝ] E3}
              {sourceU targetU : Set E3},
              sourceU ∈ 𝓝 v →
              ContinuousOn sourceEndpoint sourceU →
              (∀ q ∈ sourceU,
                HasFDerivAt (fun q' : E3 => fderiv ℝ eM q') (sourceEndpoint q) q) →
              targetU ∈ 𝓝 (L v) →
              ContinuousOn targetEndpoint targetU →
              (∀ q ∈ targetU,
                HasFDerivAt (fun q' : E3 => fderiv ℝ eS q') (targetEndpoint q) q) →
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
      CanonicalC1.exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_canonical_fderiv_c1
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
    ⟨hvsrc, hvtgt, hsource_at, htarget_at, hsource_near, htarget_near, hconsume⟩
  exact
    ⟨hvsrc, hvtgt, hsource_at, htarget_at, hsource_near, htarget_near, by
      intro sourceEndpoint targetEndpoint sourceU targetU hsourceU hsource_cont
        hsource_deriv htargetU htarget_cont htarget_deriv sourceIso hsourceIso_deriv
        hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
      have hsource_fderiv_c1 :
          ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eM q) v := by
        rw [contDiffAt_one_iff]
        exact ⟨sourceEndpoint, sourceU, hsourceU, hsource_cont, hsource_deriv⟩
      have htarget_fderiv_c1 :
          ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eS q) (L v) := by
        rw [contDiffAt_one_iff]
        exact ⟨targetEndpoint, targetU, htargetU, htarget_cont, htarget_deriv⟩
      exact
        hconsume hsource_fderiv_c1 htarget_fderiv_c1
          (sourceIso := sourceIso) hsourceIso_deriv hG₀ hG₁
          b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w⟩

end EndpointContinuity
end Poincare
