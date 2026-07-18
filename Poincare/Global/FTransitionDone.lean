import Poincare.Global.CongruenceStep

/-!
# Cartan F-transition assembly boundary

This module assembles the exported Cartan differential field, the
open-neighborhood endpoint congruence step, the residual-to-Frechet upgrade,
the local pullback germ, and the signed Christoffel transport algebra.

The remaining input is stated in the exact endpoint-derivative form needed to
start the chain: an open neighborhood on which an endpoint derivative field
agrees with `q ↦ fderiv ℝ F q`, together with its Frechet derivative at the
punctured endpoint.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace FTransitionDone

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The strongest current assembly of the Cartan F-transition law.

For each punctured normal-coordinate endpoint, this theorem proves the signed
Christoffel transition law from the single missing endpoint-regularity bridge:
an open agreement neighborhood between the canonical derivative field
`q ↦ fderiv ℝ F q` and an endpoint field whose derivative is known at the
endpoint.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_endpoint_hasFDerivAt_on_open
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
          HasStrictFDerivAt F (DF v) (eM v) ∧
            (v ∈ eM.source →
            ∀ (endpoint : E3 → E3 →L[ℝ] E3)
              (CLM : E3 →L[ℝ] E3 →L[ℝ] E3) (U : Set E3),
              IsOpen U →
              eM v ∈ U →
              Set.EqOn (fun q : E3 => fderiv ℝ F q) endpoint U →
              HasFDerivAt endpoint CLM (eM v) →
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
                      (CLM u) w) := by
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
  rcases hfield v hv hvne with
    ⟨_hsourceStrict, _htargetStrict, hDFinv, hFstrict, hpullDF⟩
  refine ⟨by simpa [F] using hFstrict, ?_⟩
  intro hvsrc endpoint CLM U hU hqU hEq hendpoint hC2 hG₀ hG₁
    b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
  let D : E3 → E3 →L[ℝ] E3 := fun q => DF (eM.symm q)
  have hD_at : D (eM v) = DF v := by
    simp [D, eM.left_inv hvsrc]
  have hFz : F (eM v) = eS (L v) := by
    change eS (L (eM.symm (eM v))) = eS (L v)
    rw [eM.left_inv hvsrc]
  have hnear_base :
      HasFDerivAt F (DF (eM.symm (eM v))) (eM v) := by
    simpa [F, eM.left_inv hvsrc] using hFstrict.hasFDerivAt
  have hbase_fderiv :
      DF (eM.symm (eM v)) = fderiv ℝ F (eM v) :=
    hnear_base.fderiv.symm
  have hres_symm :=
    CongruenceStep.fderiv_directional_residual_and_symm_of_endpoint_hasFDerivAt_on_open
      (F := F) (q := eM v) (endpoint := endpoint) (CLM := CLM)
      (U := U) hU hqU hEq hendpoint hC2
  rcases hres_symm with ⟨hres, hCLMsymm⟩
  let P : Set E3 := {q | ‖q‖ < ρ ∧ q ≠ 0}
  have hP_open : IsOpen P := by
    have hball_open : IsOpen {q : E3 | ‖q‖ < ρ} := by
      simpa [Metric.ball, dist_eq_norm] using
        (Metric.isOpen_ball (x := (0 : E3)) (ε := ρ))
    have hne_open : IsOpen {q : E3 | q ≠ 0} := isOpen_ne
    exact hball_open.inter hne_open
  have hvP : v ∈ P := ⟨hv, hvne⟩
  have hvP_symm : eM.symm (eM v) ∈ P := by
    simpa [eM.left_inv hvsrc] using hvP
  have htarget_nhds : eM.target ∈ 𝓝 (eM v) :=
    eM.open_target.mem_nhds (eM.map_source hvsrc)
  have hsymm_preimage : {q : E3 | eM.symm q ∈ P} ∈ 𝓝 (eM v) :=
    (eM.continuousAt_symm (eM.map_source hvsrc)).preimage_mem_nhds
      (hP_open.mem_nhds hvP_symm)
  have hnear :
      ∀ᶠ q in 𝓝 (eM v), q ∈ eM.target ∧ eM.symm q ∈ P := by
    filter_upwards [htarget_nhds, hsymm_preimage] with q hqtarget hqP
    exact ⟨hqtarget, hqP⟩
  have hnear_deriv :
      ∀ᶠ δ in 𝓝 (0 : E3),
        HasFDerivAt F (DF (eM.symm (eM v + δ))) (eM v + δ) := by
    have hshift :
        Tendsto (fun δ : E3 => eM v + δ) (𝓝 (0 : E3)) (𝓝 (eM v)) := by
      simpa using
        (tendsto_const_nhds.add tendsto_id :
          Tendsto (fun δ : E3 => eM v + δ) (𝓝 (0 : E3)) (𝓝 (eM v + 0)))
    filter_upwards [hshift.eventually hnear] with δ hδ
    rcases hδ with ⟨hqtarget, hqP⟩
    rcases hfield (eM.symm (eM v + δ)) hqP.1 hqP.2 with
      ⟨_, _, _, hstrict, _⟩
    have hq_eq : eM (eM.symm (eM v + δ)) = eM v + δ :=
      eM.right_inv hqtarget
    have hderiv :
        HasFDerivAt F (DF (eM.symm (eM v + δ)))
          (eM (eM.symm (eM v + δ))) := by
      simpa [F] using hstrict.hasFDerivAt
    rwa [hq_eq] at hderiv
  have hD_CLM : HasFDerivAt D CLM (eM v) := by
    apply
      GeodesicTransport.chartField_hasFDerivAt_of_directional_residual_norm_le
        (eM_symm := eM.symm) (DF := DF) (q := eM v) (CLM := CLM)
    intro c hc
    filter_upwards [hres c hc, hnear_deriv] with δ hδ hδ_deriv
    intro ξ
    have hδ_fderiv :
        DF (eM.symm (eM v + δ)) = fderiv ℝ F (eM v + δ) :=
      hδ_deriv.fderiv.symm
    calc
      ‖(DF (eM.symm (eM v + δ)) - DF (eM.symm (eM v)) - CLM δ) ξ‖
          =
        ‖(fderiv ℝ F (eM v + δ) - fderiv ℝ F (eM v) - CLM δ) ξ‖ := by
          rw [hδ_fderiv, hbase_fderiv]
      _ ≤ (c * ‖δ‖) * ‖ξ‖ := hδ ξ
  have hD : HasFDerivAt D (fderiv ℝ D (eM v)) (eM v) := by
    simpa [hD_CLM.fderiv] using hD_CLM
  have hD2symm : ∀ a b : E3,
      (fderiv ℝ D (eM v) a) b = (fderiv ℝ D (eM v) b) a := by
    intro a b
    rw [hD_CLM.fderiv]
    exact hCLMsymm a b
  have hpull_germ : ∀ a b : E3,
      (fun q : E3 => G₁ (F q) (D q a) (D q b)) =ᶠ[𝓝 (eM v)]
        (fun q : E3 => G₀ q a b) := by
    intro a b
    filter_upwards [hnear] with q hq
    rcases hfield (eM.symm q) hq.2.1 hq.2.2 with
      ⟨_, _, _, _, hpull⟩
    have hq_eq : eM (eM.symm q) = q := eM.right_inv hq.1
    calc
      G₁ (F q) (D q a) (D q b)
          =
        G₁
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L (eM.symm q)))
          (DF (eM.symm q) a) (DF (eM.symm q) b) := by
            simp [F, D, eM, CartanDifferential.cartanChartMap, G₁]
      _ = G₀ (eM (eM.symm q)) a b := by
            simpa [G₀, G₁, eM] using hpull a b
      _ = G₀ q a b := by
            rw [hq_eq]
  have hsigma : HasFDerivAt F (D (eM v)) (eM v) := by
    rw [hD_at]
    simpa [F] using hFstrict.hasFDerivAt
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
  have htransport :=
    GeodesicTransport.christoffelAt_map_eq_signed_transport_of_differentiated_pullback
      (G₀ := G₀) (G₁ := G₁) (F := F) (D := D) (z := eM v)
      (by simpa [hD_at] using hDFinv) hD2symm hdiff hpull hG₁symm
      b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
  simpa [D, hD_at, hD_CLM.fderiv] using htransport

end FTransitionDone
end Poincare
