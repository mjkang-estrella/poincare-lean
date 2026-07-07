import Poincare.Global.ContinuityPackages

/-!
# Indexed endpoint selection boundary

This module isolates the final consumer step for a neighborhood-indexed
third-variation endpoint package.  It does not manufacture the hosted
`q ↦ ζ_q, Ω_q, D_q` data; it proves that once the resulting source and target
endpoint Gronwall packages are available at each punctured normal vector, the
remaining endpoint callback in `ContinuityPackages` is discharged.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace IndexedSelection

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Pointwise indexed endpoint Gronwall packages fire the produced-field
F-transition tower.

The remaining nontrivial producer is the hypothesis grouped here as an
existential package: source and target endpoint CLM fields on neighborhoods of
the selected source/target normal vectors, their Gronwall bounds, and their
derivative representation for the canonical `q ↦ fderiv ℝ e q` fields.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_indexed_endpoint_gronwall_packages
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
            ((∃ sourceEndpoint :
                E3 → E3 →L[ℝ] E3 →L[ℝ] E3,
              ∃ targetEndpoint :
                E3 → E3 →L[ℝ] E3 →L[ℝ] E3,
              ∃ sourceU : Set E3,
              ∃ targetU : Set E3,
              ∃ Ks Kt : ℝ≥0,
                sourceU ∈ 𝓝 v ∧
                  (∀ q ∈ sourceU, ∀ q' ∈ sourceU,
                    ‖sourceEndpoint q' - sourceEndpoint q‖ ≤
                      (Ks : ℝ) * dist q' q) ∧
                  (∀ q ∈ sourceU,
                    HasFDerivAt
                      (fun q' : E3 => fderiv ℝ eM q')
                      (sourceEndpoint q) q) ∧
                  targetU ∈ 𝓝 (L v) ∧
                  (∀ q ∈ targetU, ∀ q' ∈ targetU,
                    ‖targetEndpoint q' - targetEndpoint q‖ ≤
                      (Kt : ℝ) * dist q' q) ∧
                  ∀ q ∈ targetU,
                    HasFDerivAt
                      (fun q' : E3 => fderiv ℝ eS q')
                      (targetEndpoint q) q) →
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
      _root_.Poincare.ContinuityPackages.exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_gronwall_endpoint_bounds
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
      intro hindexed sourceIso hsourceIso_deriv hG₀ hG₁ b₀ b₁ hb₀ hb₁
        hb₀G hb₁G u w
      rcases hindexed with
        ⟨sourceEndpoint, targetEndpoint, sourceU, targetU, Ks, Kt,
          hsourceU, hsource_bound, hsource_deriv, htargetU, htarget_bound,
          htarget_deriv⟩
      exact
        hconsume
          (sourceEndpoint := sourceEndpoint) (targetEndpoint := targetEndpoint)
          (sourceU := sourceU) (targetU := targetU) (Ks := Ks) (Kt := Kt)
          hsourceU hsource_bound hsource_deriv htargetU htarget_bound
          htarget_deriv (sourceIso := sourceIso) hsourceIso_deriv hG₀ hG₁
          b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w⟩

end IndexedSelection
end Poincare
