import Poincare.Global.FTransitionDone
import Poincare.Global.UniformTangentAlignmentDifferentialField

/-!
# Fixed-anchor F-transition radius uniform over tangent alignments

The endpoint-congruence and differentiated-pullback argument in
`FTransitionDone` consumes only a differential field on a punctured ball.
Feeding it the fixed-anchor field whose radius precedes the tangent alignment
therefore preserves that quantifier order through the full raw Christoffel
transition package.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UniformTangentAlignmentFTransition

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
For fixed anchors, one positive punctured-ball radius supports the raw Cartan
F-transition package for every tangent alignment.  The differential fields
and their selected equivalences may depend on the alignment; the radius does
not.
-/
theorem exists_uniform_cartanChartMap_christoffelAt_F_transition_law_of_endpoint_hasFDerivAt_on_open
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x₀ p₀,
        ∃ Afield Bfield : E → E ≃L[ℝ] E,
        ∃ DF : E → E →L[ℝ] E,
          (∀ v : E,
            DF v =
              CartanLocalIsometry.cartanChartDifferential
                L (Afield v) (Bfield v)) ∧
          ∀ v : E, ‖v‖ < rho → v ≠ 0 →
            let eM :=
              GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
            let F := CartanDifferential.cartanChartMap g x₀ p₀ L
            let G₀ : E → E →L[ℝ] E →L[ℝ] ℝ :=
              fun z => CovariantDerivative.chartMetric g.inner x₀ z
            let G₁ : E → E →L[ℝ] E →L[ℝ] ℝ :=
              fun z =>
                CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
            HasStrictFDerivAt F (DF v) (eM v) ∧
              (v ∈ eM.source →
              ∀ (endpoint : E → E →L[ℝ] E)
                (CLM : E →L[ℝ] E →L[ℝ] E) (U : Set E),
                IsOpen U →
                eM v ∈ U →
                Set.EqOn (fun q : E => fderiv ℝ F q) endpoint U →
                HasFDerivAt endpoint CLM (eM v) →
                ContDiffAt ℝ 2 F (eM v) →
                HasFDerivAt G₀ (fderiv ℝ G₀ (eM v)) (eM v) →
                HasFDerivAt G₁ (fderiv ℝ G₁ (F (eM v))) (F (eM v)) →
                ∀ (b₀ b₁ : LinearMap.BilinForm ℝ E)
                  (hb₀ : b₀.Nondegenerate) (hb₁ : b₁.Nondegenerate),
                  (∀ a b : E, b₀ a b = G₀ (eM v) a b) →
                  (∀ a b : E, b₁ a b = G₁ (F (eM v)) a b) →
                  ∀ u w : E,
                    CovariantDerivative.christoffelAt G₁ (F (eM v)) b₁
                        hb₁ (DF v w) (DF v u) =
                      DF v
                          (CovariantDerivative.christoffelAt G₀ (eM v) b₀
                            hb₀ w u) -
                        (CLM u) w) := by
  rcases
      UniformTangentAlignmentDifferentialField.exists_uniform_cartanChartDifferential_field_on_punctured_ball
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) with
    ⟨rho, hrho_pos, hfields⟩
  refine ⟨rho, hrho_pos, ?_⟩
  intro L
  rcases hfields L with
    ⟨Afield, Bfield, DF, hDF_def, hfield⟩
  refine ⟨Afield, Bfield, DF, hDF_def, ?_⟩
  intro v hv hvne
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀
  let F := CartanDifferential.cartanChartMap g x₀ p₀ L
  let G₀ : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric g.inner x₀ z
  let G₁ : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
  rcases hfield v hv hvne with
    ⟨_hsourceStrict, _htargetStrict, hDFinv, hFstrict, hpullDF⟩
  refine ⟨by simpa [F] using hFstrict, ?_⟩
  intro hvsrc endpoint CLM U hU hqU hEq hendpoint hC2 hG₀ hG₁
    b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
  let D : E → E →L[ℝ] E := fun q => DF (eM.symm q)
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
  let P : Set E := {q | ‖q‖ < rho ∧ q ≠ 0}
  have hP_open : IsOpen P := by
    have hball_open : IsOpen {q : E | ‖q‖ < rho} := by
      simpa [Metric.ball, dist_eq_norm] using
        (Metric.isOpen_ball (x := (0 : E)) (ε := rho))
    have hne_open : IsOpen {q : E | q ≠ 0} := isOpen_ne
    exact hball_open.inter hne_open
  have hvP : v ∈ P := ⟨hv, hvne⟩
  have hvP_symm : eM.symm (eM v) ∈ P := by
    simpa [eM.left_inv hvsrc] using hvP
  have htarget_nhds : eM.target ∈ 𝓝 (eM v) :=
    eM.open_target.mem_nhds (eM.map_source hvsrc)
  have hsymm_preimage : {q : E | eM.symm q ∈ P} ∈ 𝓝 (eM v) :=
    (eM.continuousAt_symm (eM.map_source hvsrc)).preimage_mem_nhds
      (hP_open.mem_nhds hvP_symm)
  have hnear :
      ∀ᶠ q in 𝓝 (eM v), q ∈ eM.target ∧ eM.symm q ∈ P := by
    filter_upwards [htarget_nhds, hsymm_preimage] with q hqtarget hqP
    exact ⟨hqtarget, hqP⟩
  have hnear_deriv :
      ∀ᶠ delta in 𝓝 (0 : E),
        HasFDerivAt F (DF (eM.symm (eM v + delta))) (eM v + delta) := by
    have hshift :
        Tendsto (fun delta : E => eM v + delta) (𝓝 (0 : E)) (𝓝 (eM v)) := by
      simpa using
        (tendsto_const_nhds.add tendsto_id :
          Tendsto (fun delta : E => eM v + delta) (𝓝 (0 : E)) (𝓝 (eM v + 0)))
    filter_upwards [hshift.eventually hnear] with delta hdelta
    rcases hdelta with ⟨hqtarget, hqP⟩
    rcases hfield (eM.symm (eM v + delta)) hqP.1 hqP.2 with
      ⟨_, _, _, hstrict, _⟩
    have hq_eq : eM (eM.symm (eM v + delta)) = eM v + delta :=
      eM.right_inv hqtarget
    have hderiv :
        HasFDerivAt F (DF (eM.symm (eM v + delta)))
          (eM (eM.symm (eM v + delta))) := by
      simpa [F] using hstrict.hasFDerivAt
    rwa [hq_eq] at hderiv
  have hD_CLM : HasFDerivAt D CLM (eM v) := by
    apply
      GeodesicTransport.chartField_hasFDerivAt_of_directional_residual_norm_le
        (eM_symm := eM.symm) (DF := DF) (q := eM v) (CLM := CLM)
    intro c hc
    filter_upwards [hres c hc, hnear_deriv] with delta hdelta hdelta_deriv
    intro xi
    have hdelta_fderiv :
        DF (eM.symm (eM v + delta)) = fderiv ℝ F (eM v + delta) :=
      hdelta_deriv.fderiv.symm
    calc
      ‖(DF (eM.symm (eM v + delta)) - DF (eM.symm (eM v)) - CLM delta) xi‖
          =
        ‖(fderiv ℝ F (eM v + delta) - fderiv ℝ F (eM v) - CLM delta) xi‖ := by
          rw [hdelta_fderiv, hbase_fderiv]
      _ ≤ (c * ‖delta‖) * ‖xi‖ := hdelta xi
  have hD : HasFDerivAt D (fderiv ℝ D (eM v)) (eM v) := by
    simpa [hD_CLM.fderiv] using hD_CLM
  have hD2symm : ∀ a b : E,
      (fderiv ℝ D (eM v) a) b = (fderiv ℝ D (eM v) b) a := by
    intro a b
    rw [hD_CLM.fderiv]
    exact hCLMsymm a b
  have hpull_germ : ∀ a b : E,
      (fun q : E => G₁ (F q) (D q a) (D q b)) =ᶠ[𝓝 (eM v)]
        (fun q : E => G₀ q a b) := by
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
      ∀ e a b : E,
        ((fderiv ℝ G₁ (F (eM v)) (D (eM v) e)) (D (eM v) a)
            (D (eM v) b)) +
          G₁ (F (eM v)) ((fderiv ℝ D (eM v) e) a) (D (eM v) b) +
          G₁ (F (eM v)) (D (eM v) a)
            ((fderiv ℝ D (eM v) e) b) =
        ((fderiv ℝ G₀ (eM v) e) a b) :=
    GeodesicTransport.differentiated_pullback_hdiff_of_eventuallyEq
      (G0 := G₀) (G1 := G₁) (sigma := F) (D := D)
      hsigma hD hG₀ hG₁ hpull_germ
  have hpull : ∀ a b : E,
      G₁ (F (eM v)) (D (eM v) a) (D (eM v) b) =
        G₀ (eM v) a b := by
    intro a b
    rw [hFz, hD_at]
    simpa [G₀, G₁, eM, eS] using hpullDF a b
  have hG₁symm : ∀ a b : E,
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

end UniformTangentAlignmentFTransition
end Poincare
