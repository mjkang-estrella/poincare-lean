import Poincare.Global.HostedCLM
import Poincare.Global.EndpointContinuity

/-!
# Continuity packages for endpoint fields

This module isolates the non-vacuous continuity conversion needed by the
level-three endpoint package: a uniform Gronwall-type norm bound for a
CLM-valued endpoint field gives `LipschitzOnWith`, hence `ContinuousOn`, and
therefore the `contDiffAt_one_iff` package consumed by `EndpointContinuity`.
-/

noncomputable section

open Filter Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace ContinuityPackages

/-- A pointwise distance bound in the Gronwall shape gives a Lipschitz package. -/
theorem lipschitzOnWith_of_dist_bound
    {ι Y : Type*} [PseudoMetricSpace ι] [PseudoMetricSpace Y]
    {K : ℝ≥0} {s : Set ι} {f : ι → Y}
    (hbound : ∀ x ∈ s, ∀ y ∈ s,
      dist (f y) (f x) ≤ (K : ℝ) * dist y x) :
    LipschitzOnWith K f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa [dist_comm] using hbound x hx y hy

/--
A pointwise distance bound in the Gronwall shape gives continuity on the same
set.  This is the exact `LipschitzOnWith.continuousOn` conversion needed for
endpoint CLM fields.
-/
theorem continuousOn_of_dist_bound
    {ι Y : Type*} [PseudoMetricSpace ι] [PseudoMetricSpace Y]
    {K : ℝ≥0} {s : Set ι} {f : ι → Y}
    (hbound : ∀ x ∈ s, ∀ y ∈ s,
      dist (f y) (f x) ≤ (K : ℝ) * dist y x) :
    ContinuousOn f s :=
  (lipschitzOnWith_of_dist_bound (K := K) (s := s) (f := f) hbound).continuousOn

/-- Norm-subtraction form of the endpoint-field Lipschitz conversion. -/
theorem normedField_lipschitzOnWith_of_norm_sub_le
    {ι Y : Type*} [PseudoMetricSpace ι] [NormedAddCommGroup Y]
    {K : ℝ≥0} {s : Set ι} {F : ι → Y}
    (hbound : ∀ x ∈ s, ∀ y ∈ s,
      ‖F y - F x‖ ≤ (K : ℝ) * dist y x) :
    LipschitzOnWith K F s := by
  apply lipschitzOnWith_of_dist_bound (K := K) (s := s) (f := F)
  intro x hx y hy
  simpa [dist_eq_norm] using hbound x hx y hy

/-- Norm-subtraction form of the endpoint-field continuity conversion. -/
theorem normedField_continuousOn_of_norm_sub_le
    {ι Y : Type*} [PseudoMetricSpace ι] [NormedAddCommGroup Y]
    {K : ℝ≥0} {s : Set ι} {F : ι → Y}
    (hbound : ∀ x ∈ s, ∀ y ∈ s,
      ‖F y - F x‖ ≤ (K : ℝ) * dist y x) :
    ContinuousOn F s :=
  (normedField_lipschitzOnWith_of_norm_sub_le
    (K := K) (s := s) (F := F) hbound).continuousOn

/--
Endpoint continuity and the local derivative representation assemble the
canonical `C1` package for `q ↦ fderiv ℝ F q`.
-/
theorem contDiffAt_one_fderiv_of_endpoint_continuity
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {q : E}
    {endpoint : E → E →L[ℝ] (E →L[ℝ] G)} {U : Set E}
    (hU : U ∈ 𝓝 q)
    (hcont : ContinuousOn endpoint U)
    (hderiv : ∀ q' ∈ U,
      HasFDerivAt (fun z : E => fderiv ℝ F z) (endpoint q') q') :
    ContDiffAt ℝ 1 (fun z : E => fderiv ℝ F z) q := by
  rw [contDiffAt_one_iff]
  exact ⟨endpoint, U, hU, hcont, hderiv⟩

local notation "E3" => ClosedSmoothModel 3

/-- Source and target endpoint-continuity packages give the two canonical C1 facts. -/
theorem source_target_fderiv_contDiffAt_one_of_endpoint_continuity
    {eM eS : E3 → E3} {v w : E3}
    {sourceEndpoint targetEndpoint : E3 → E3 →L[ℝ] (E3 →L[ℝ] E3)}
    {sourceU targetU : Set E3}
    (hsourceU : sourceU ∈ 𝓝 v)
    (hsource_cont : ContinuousOn sourceEndpoint sourceU)
    (hsource_deriv : ∀ q ∈ sourceU,
      HasFDerivAt (fun q' : E3 => fderiv ℝ eM q') (sourceEndpoint q) q)
    (htargetU : targetU ∈ 𝓝 w)
    (htarget_cont : ContinuousOn targetEndpoint targetU)
    (htarget_deriv : ∀ q ∈ targetU,
      HasFDerivAt (fun q' : E3 => fderiv ℝ eS q') (targetEndpoint q) q) :
    ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eM q) v ∧
      ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eS q) w :=
  ⟨contDiffAt_one_fderiv_of_endpoint_continuity
      (F := eM) hsourceU hsource_cont hsource_deriv,
    contDiffAt_one_fderiv_of_endpoint_continuity
      (F := eS) htargetU htarget_cont htarget_deriv⟩

/--
Gronwall-style endpoint bounds for source and target endpoint fields assemble
the two canonical `C1` facts demanded by `CanonicalC1`.
-/
theorem source_target_fderiv_contDiffAt_one_of_gronwall_endpoint_bounds
    {eM eS : E3 → E3} {v w : E3}
    {sourceEndpoint targetEndpoint : E3 → E3 →L[ℝ] (E3 →L[ℝ] E3)}
    {sourceU targetU : Set E3} {Ks Kt : ℝ≥0}
    (hsourceU : sourceU ∈ 𝓝 v)
    (hsource_bound : ∀ q ∈ sourceU, ∀ q' ∈ sourceU,
      ‖sourceEndpoint q' - sourceEndpoint q‖ ≤ (Ks : ℝ) * dist q' q)
    (hsource_deriv : ∀ q ∈ sourceU,
      HasFDerivAt (fun q' : E3 => fderiv ℝ eM q') (sourceEndpoint q) q)
    (htargetU : targetU ∈ 𝓝 w)
    (htarget_bound : ∀ q ∈ targetU, ∀ q' ∈ targetU,
      ‖targetEndpoint q' - targetEndpoint q‖ ≤ (Kt : ℝ) * dist q' q)
    (htarget_deriv : ∀ q ∈ targetU,
      HasFDerivAt (fun q' : E3 => fderiv ℝ eS q') (targetEndpoint q) q) :
    ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eM q) v ∧
      ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eS q) w := by
  have hsource_cont : ContinuousOn sourceEndpoint sourceU :=
    normedField_continuousOn_of_norm_sub_le
      (K := Ks) (s := sourceU) (F := sourceEndpoint) hsource_bound
  have htarget_cont : ContinuousOn targetEndpoint targetU :=
    normedField_continuousOn_of_norm_sub_le
      (K := Kt) (s := targetU) (F := targetEndpoint) htarget_bound
  exact
    source_target_fderiv_contDiffAt_one_of_endpoint_continuity
      (eM := eM) (eS := eS) (v := v) (w := w)
      hsourceU hsource_cont hsource_deriv
      htargetU htarget_cont htarget_deriv

universe u

local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The produced-field F-transition tower can be fed by Gronwall-style endpoint
continuity packages on both source and target sides.

Compared with `EndpointContinuity`, this removes the explicit `ContinuousOn`
assumptions from the callback and replaces them by uniform endpoint-field norm
bounds, using the Lipschitz/continuity conversion above.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_gronwall_endpoint_bounds
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
              {sourceU targetU : Set E3} {Ks Kt : ℝ≥0},
              sourceU ∈ 𝓝 v →
              (∀ q ∈ sourceU, ∀ q' ∈ sourceU,
                ‖sourceEndpoint q' - sourceEndpoint q‖ ≤
                  (Ks : ℝ) * dist q' q) →
              (∀ q ∈ sourceU,
                HasFDerivAt (fun q' : E3 => fderiv ℝ eM q') (sourceEndpoint q) q) →
              targetU ∈ 𝓝 (L v) →
              (∀ q ∈ targetU, ∀ q' ∈ targetU,
                ‖targetEndpoint q' - targetEndpoint q‖ ≤
                  (Kt : ℝ) * dist q' q) →
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
      EndpointContinuity.exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_endpoint_continuity
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
      intro sourceEndpoint targetEndpoint sourceU targetU Ks Kt hsourceU
        hsource_bound hsource_deriv htargetU htarget_bound htarget_deriv
        sourceIso hsourceIso_deriv hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
      have hsource_cont : ContinuousOn sourceEndpoint sourceU :=
        normedField_continuousOn_of_norm_sub_le
          (K := Ks) (s := sourceU) (F := sourceEndpoint) hsource_bound
      have htarget_cont : ContinuousOn targetEndpoint targetU :=
        normedField_continuousOn_of_norm_sub_le
          (K := Kt) (s := targetU) (F := targetEndpoint) htarget_bound
      exact
        hconsume hsourceU hsource_cont hsource_deriv
          htargetU htarget_cont htarget_deriv
          (sourceIso := sourceIso) hsourceIso_deriv hG₀ hG₁
          b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w⟩

end ContinuityPackages
end Poincare
