import Poincare.Global.DifferentialField
import Poincare.Global.EndpointBridge
import Poincare.Global.FieldProducer
import Poincare.Global.UniformAnchoredSecondVariation

/-!
# Uniform anchored regularity closes the Cartan F-transition boundary

This module intersects the actual second-variation `C²` radii with the
curvature-rigidity differential field.  The source endpoint equivalence carried
by the rigidity construction discharges the inverse-function hypothesis, and
the resulting Cartan-map `C²` fact feeds the existing endpoint F-transition
consumer.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UniformAnchoredFTransition

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/-- The underlying algebraic bilinear form of a continuous bilinear map. -/
def chartMetricBilin (G : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
    LinearMap.BilinForm ℝ E3 :=
  LinearMap.mk₂ ℝ (fun v w => G v w)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp]
theorem chartMetricBilin_apply
    (G : E3 →L[ℝ] E3 →L[ℝ] ℝ) (v w : E3) :
    chartMetricBilin G v w = G v w := rfl

/-- Smoothness of the Riemannian metric section gives `C¹` regularity of its
bilinear-form-valued chart metric at every point of the inverse-chart target. -/
theorem chartMetric_contDiffAt_one_of_mem_target
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {z : E3}
    (hz : z ∈ (extChartAt I3 x₀).target) :
    ContDiffAt ℝ 1 (CovariantDerivative.chartMetric g.inner x₀) z := by
  have hone_le_top : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) = ((1 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hone_add_one_le_top : (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) + 1 = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg1 :
      ContMDiff I3 ((I3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) 1
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E3 →L[ℝ] E3 →L[ℝ] ℝ)
              (fun y : M =>
                TangentSpace I3 y →L[ℝ] TangentSpace I3 y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le hone_le_top
  apply Poincare.contDiffAt_clm_of_apply
  intro v
  apply Poincare.contDiffAt_clm_of_apply
  intro w
  have hscalar :=
    CovariantDerivative.contMDiffOn_chartMetric_pairing
      g.inner x₀ hone_add_one_le_top hg1 v w z hz
  exact
    contMDiffAt_iff_contDiffAt.mp
      (hscalar.contMDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hz))

/-- The chart metric has its canonical Fréchet derivative at every point of
the inverse-chart target. -/
theorem chartMetric_hasFDerivAt_of_mem_target
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {z : E3}
    (hz : z ∈ (extChartAt I3 x₀).target) :
    HasFDerivAt
      (CovariantDerivative.chartMetric g.inner x₀)
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z) z :=
  ((chartMetric_contDiffAt_one_of_mem_target g x₀ hz).differentiableAt
    (by norm_num)).hasFDerivAt

/-- The actual algebraic chart metric is nondegenerate on the inverse-chart
target. -/
theorem chartMetricBilin_nondegenerate_of_mem_target
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {z : E3}
    (hz : z ∈ (extChartAt I3 x₀).target) :
    (chartMetricBilin
      (CovariantDerivative.chartMetric g.inner x₀ z)).Nondegenerate := by
  have hgnd :
      ∀ (y : M) (v : TangentSpace I3 y),
        (∀ w, g.inner y v w = 0) → v = 0 := by
    intro y v hv
    by_contra hvne
    exact (ne_of_gt (g.inner_pos y hvne)) (hv v)
  have hinv := isInvertible_mfderivWithin_extChartAt_symm hz
  have hleft :
      ∀ v : E3,
        (∀ w, CovariantDerivative.chartMetric g.inner x₀ z v w = 0) →
        v = 0 :=
    CovariantDerivative.chartMetric_nondegenerate g.inner hgnd x₀ hinv
  constructor
  · intro v hv
    apply hleft v
    intro w
    simpa using hv w
  · intro v hv
    apply hleft v
    intro w
    rw [CovariantDerivative.chartMetric_symm g.inner
      (fun y a b => g.inner_symm y a b)]
    simpa using hv w

/-- Constant curvature supplies the invertible source exponential derivative
needed by the uniform anchored Cartan `C²` theorem.  The radius is also shrunk
so that source and aligned target vectors lie in their exponential-chart
domains. -/
theorem exists_cartanChartMap_contDiffAt_two_on_punctured_ball
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
          let eM :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
          let eS :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀
          let F := CartanDifferential.cartanChartMap g x₀ p₀ L
          v ∈ eM.source ∧
            L v ∈ eS.source ∧
            eM v ∈ (extChartAt I3 x₀).target ∧
            eS (L v) ∈ (extChartAt I3 p₀).target ∧
            HasStrictFDerivAt eM (Afield v : E3 →L[ℝ] E3) v ∧
            ContDiffAt ℝ 2 F (eM v) := by
  rcases
      DifferentialField.exists_cartanChartDifferential_field_on_punctured_ball
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρd, hρd, Afield, Bfield, DF, hDF, hdiff⟩
  rcases
      FieldProducer.exists_source_target_expChart_derivative_fields_on_aligned_ball
        (g := g) (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρp, hρp, _sourceD, _targetD, hdomains⟩
  rcases
      UniformAnchoredSecondVariation.exists_cartanChartMap_contDiffAt_two_on_small_normal_balls
        (g := g) (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρs, hρs, ρt, hρt, hC2⟩
  rcases
      GeodesicTransport.expAt_mem_source_of_norm_lt (g := g) (x₀ := x₀) with
    ⟨ρms, hρms, hsourceChart⟩
  rcases
      GeodesicTransport.expAt_mem_source_of_norm_lt
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨ρmt, hρmt, htargetChart⟩
  let C : ℝ := ‖(L.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ + 1
  let ρsource : ℝ := min ρd (min ρp (min ρs ρms))
  let ρtarget : ℝ := min ρt ρmt
  let ρ : ℝ := min ρsource (ρtarget / C)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hρsource : 0 < ρsource := by
    dsimp [ρsource]
    exact lt_min hρd (lt_min hρp (lt_min hρs hρms))
  have hρtarget : 0 < ρtarget := by
    dsimp [ρtarget]
    exact lt_min hρt hρmt
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρsource (div_pos hρtarget hC)
  refine ⟨ρ, hρ, Afield, Bfield, DF, hDF, ?_⟩
  intro v hv hvne
  dsimp only
  have hvsource : ‖v‖ < ρsource :=
    hv.trans_le (min_le_left ρsource (ρtarget / C))
  have hvd : ‖v‖ < ρd :=
    hvsource.trans_le (min_le_left ρd (min ρp (min ρs ρms)))
  have hvp : ‖v‖ < ρp :=
    hvsource.trans_le
      ((min_le_right ρd (min ρp (min ρs ρms))).trans
        (min_le_left ρp (min ρs ρms)))
  have hvs : ‖v‖ < ρs :=
    hvsource.trans_le
      (((min_le_right ρd (min ρp (min ρs ρms))).trans
        (min_le_right ρp (min ρs ρms))).trans (min_le_left ρs ρms))
  have hvms : ‖v‖ < ρms :=
    hvsource.trans_le
      (((min_le_right ρd (min ρp (min ρs ρms))).trans
        (min_le_right ρp (min ρs ρms))).trans (min_le_right ρs ρms))
  have hvtarget : ‖v‖ < ρtarget / C :=
    hv.trans_le (min_le_right ρsource (ρtarget / C))
  have hLvTarget : ‖L v‖ < ρtarget := by
    have hop :
        ‖L v‖ ≤ ‖(L.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (L.toContinuousLinearEquiv : E3 →L[ℝ] E3) v
    have hopC :
        ‖(L.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (norm_nonneg v)
    have hmul : C * ‖v‖ < ρtarget := by
      calc
        C * ‖v‖ < C * (ρtarget / C) := mul_lt_mul_of_pos_left hvtarget hC
        _ = ρtarget := by field_simp [ne_of_gt hC]
    exact lt_of_le_of_lt (hop.trans hopC) hmul
  have hLv : ‖L v‖ < ρt :=
    hLvTarget.trans_le (min_le_left ρt ρmt)
  have hLvmt : ‖L v‖ < ρmt :=
    hLvTarget.trans_le (min_le_right ρt ρmt)
  rcases hdomains v hvp with
    ⟨hvsrc, hvtgt, _hsourceAt, _htargetAt, _hsourceNear, _htargetNear⟩
  rcases hdiff v hvd hvne with
    ⟨hsourceStrict, _htargetStrict, _hDFinv, _hFstrict, _hpullback⟩
  have hvs_ball : v ∈ ball (0 : E3) ρs := by
    simpa [mem_ball, dist_eq_norm] using hvs
  have hLv_ball : L v ∈ ball (0 : E3) ρt := by
    simpa [mem_ball, dist_eq_norm] using hLv
  have heM_chart :
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v ∈
        (extChartAt I3 x₀).target := by
    exact (extChartAt I3 x₀).map_source (hsourceChart v hvms)
  have heS_chart :
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v) ∈
        (extChartAt I3 p₀).target := by
    exact (extChartAt I3 p₀).map_source (htargetChart (L v) hLvmt)
  have hF_C2 :=
    hC2 v hvs_ball hLv_ball hvsrc
      ⟨Afield v, hsourceStrict.hasFDerivAt⟩
  exact ⟨hvsrc, hvtgt, heM_chart, heS_chart, hsourceStrict, hF_C2⟩

/-- The curvature-only uniform anchored `C²` theorem discharges the Cartan
regularity input of `EndpointBridge`.  The only remaining analytic inputs are
the two pointwise chart-metric derivatives; the remaining form arguments are
the algebraic representation expected by the Christoffel interface. -/
theorem exists_cartanChartMap_christoffelAt_F_transition_law
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
          let eM :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
          let eS :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀
          let F := CartanDifferential.cartanChartMap g x₀ p₀ L
          let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric g.inner x₀ z
          let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z =>
              CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
          v ∈ eM.source ∧
            L v ∈ eS.source ∧
            eM v ∈ (extChartAt I3 x₀).target ∧
            F (eM v) ∈ (extChartAt I3 p₀).target ∧
            ContDiffAt ℝ 2 F (eM v) ∧
            (HasFDerivAt G₀ (fderiv ℝ G₀ (eM v)) (eM v) →
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
      exists_cartanChartMap_contDiffAt_two_on_punctured_ball
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρc, hρc, _sourceA, _targetB, _sourceDF, _hsourceDF, hC2⟩
  rcases
      EndpointBridge.exists_cartanChartMap_christoffelAt_F_transition_law_of_contDiffAt_two
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρt, hρt, Afield, Bfield, DF, hDF, htransition⟩
  refine ⟨min ρc ρt, lt_min hρc hρt, Afield, Bfield, DF, hDF, ?_⟩
  intro v hv hvne
  dsimp only
  have hvc : ‖v‖ < ρc := hv.trans_le (min_le_left ρc ρt)
  have hvt : ‖v‖ < ρt := hv.trans_le (min_le_right ρc ρt)
  rcases hC2 v hvc hvne with
    ⟨hvsrc, hLvsrc, heMchart, heSchart, _hsourceStrict, hF_C2⟩
  have hFz :
      CartanDifferential.cartanChartMap g x₀ p₀ L
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v) := by
    change
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀)
          (L ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₀).symm
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₀) v))) = _
    rw [(GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) x₀).left_inv hvsrc]
  have hFchart :
      CartanDifferential.cartanChartMap g x₀ p₀ L
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∈
        (extChartAt I3 p₀).target := by
    rw [hFz]
    exact heSchart
  refine ⟨hvsrc, hLvsrc, heMchart, hFchart, hF_C2, ?_⟩
  intro hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
  exact
    htransition v hvt hvne hvsrc hF_C2 hG₀ hG₁
      b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w

/-- Fully curvature-only Cartan F-transition on a common punctured normal
ball.  Both chart-metric derivative facts and both algebraic nondegeneracy
witnesses are constructed from the smooth Riemannian metrics. -/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_curvature_only
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
          let eM :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
          let eS :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀
          let F := CartanDifferential.cartanChartMap g x₀ p₀ L
          let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric g.inner x₀ z
          let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z =>
              CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
          v ∈ eM.source ∧
            L v ∈ eS.source ∧
            ContDiffAt ℝ 2 F (eM v) ∧
            ∃ b₀ b₁ : LinearMap.BilinForm ℝ E3,
              ∃ hb₀ : b₀.Nondegenerate,
              ∃ hb₁ : b₁.Nondegenerate,
                (∀ a b : E3, b₀ a b = G₀ (eM v) a b) ∧
                (∀ a b : E3, b₁ a b = G₁ (F (eM v)) a b) ∧
                ∀ u w : E3,
                  CovariantDerivative.christoffelAt G₁ (F (eM v)) b₁
                      hb₁ (DF v w) (DF v u) =
                    DF v
                        (CovariantDerivative.christoffelAt G₀ (eM v) b₀
                          hb₀ w u) -
                      ((fderiv ℝ (fun q : E3 => fderiv ℝ F q) (eM v)) u) w := by
  rcases
      exists_cartanChartMap_christoffelAt_F_transition_law
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ, Afield, Bfield, DF, hDF, htransition⟩
  refine ⟨ρ, hρ, Afield, Bfield, DF, hDF, ?_⟩
  intro v hv hvne
  dsimp only
  rcases htransition v hv hvne with
    ⟨hvsrc, hLvsrc, heMchart, hFchart, hF_C2, hconsume⟩
  let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric g.inner x₀ z
  let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let F := CartanDifferential.cartanChartMap g x₀ p₀ L
  have hG₀ : HasFDerivAt G₀ (fderiv ℝ G₀ (eM v)) (eM v) := by
    simpa [G₀, eM] using
      chartMetric_hasFDerivAt_of_mem_target g x₀ heMchart
  have hG₁ : HasFDerivAt G₁ (fderiv ℝ G₁ (F (eM v))) (F (eM v)) := by
    simpa [G₁, F, eM] using
      chartMetric_hasFDerivAt_of_mem_target
        (M := RoundSphere3) roundSphereMetric3 p₀ hFchart
  let b₀ : LinearMap.BilinForm ℝ E3 := chartMetricBilin (G₀ (eM v))
  let b₁ : LinearMap.BilinForm ℝ E3 := chartMetricBilin (G₁ (F (eM v)))
  have hb₀ : b₀.Nondegenerate := by
    simpa [b₀, G₀, eM] using
      chartMetricBilin_nondegenerate_of_mem_target g x₀ heMchart
  have hb₁ : b₁.Nondegenerate := by
    simpa [b₁, G₁, F, eM] using
      chartMetricBilin_nondegenerate_of_mem_target
        (M := RoundSphere3) roundSphereMetric3 p₀ hFchart
  have hb₀G : ∀ a b : E3, b₀ a b = G₀ (eM v) a b := by
    intro a b
    rfl
  have hb₁G : ∀ a b : E3, b₁ a b = G₁ (F (eM v)) a b := by
    intro a b
    rfl
  refine ⟨hvsrc, hLvsrc, hF_C2, b₀, b₁, hb₀, hb₁, hb₀G, hb₁G, ?_⟩
  intro u w
  exact hconsume hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w

end UniformAnchoredFTransition
end Poincare
