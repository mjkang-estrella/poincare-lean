import Poincare.Global.UniformAnchoredSecondVariation
import Poincare.Global.UniformTangentAlignmentDifferentialField

/-!
# Fixed-anchor Cartan C2 radius uniform over tangent alignments

The source and target exponential-chart regularity radii in
`UniformAnchoredSecondVariation` depend only on the fixed metrics and anchors.
The tangent alignment enters only when a source vector is tested against the
target radius.  A common operator-norm bound therefore makes that regularity
radius uniform over the entire fixed-anchor alignment fiber.

The final punctured-ball assembly uses the already-uniform differential field
for the invertible source derivative.  Domain membership comes directly from
the source and target exponential-chart source balls; no `FieldProducer`
radius or derivative-field choice is needed.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UniformTangentAlignmentC2

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport
open UniformAnchoredSecondVariation

omit [T2Space M] in
/-- The inverse-function-theorem source of an exponential chart contains a
positive normal-coordinate ball. -/
theorem exists_expAtChartOpenPartialHomeomorph_mem_source_of_norm_lt
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
      v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source := by
  let e := expAtChartOpenPartialHomeomorph (g := g) x₀
  have hzero : (0 : E) ∈ e.source :=
    zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hzero) with
    ⟨r, hr, hrsub⟩
  refine ⟨r, hr, ?_⟩
  intro v hv
  apply hrsub
  simpa [mem_ball, dist_eq_norm] using hv

/--
The source and target normal-coordinate C2 radii can be selected before the
tangent alignment.  At this level the caller supplies the two ball-membership
facts, so no operator bound is needed yet.
-/
theorem exists_uniform_cartanChartMap_contDiffAt_two_on_small_normal_balls
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (p₀ : RoundSphere3) :
    ∃ rhoS > (0 : ℝ), ∃ rhoT > (0 : ℝ),
      ∀ (L : CartanMap.TangentAlignment g x₀ p₀) (v : E),
        v ∈ ball (0 : E) rhoS →
        L v ∈ ball (0 : E) rhoT →
        v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source →
        (∃ sourceIso : E ≃L[ℝ] E,
          HasFDerivAt
            (expAtChartOpenPartialHomeomorph (g := g) x₀)
            (sourceIso : E →L[ℝ] E) v) →
        ContDiffAt ℝ 2 (CartanDifferential.cartanChartMap g x₀ p₀ L)
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) := by
  rcases exists_expAtChart_hasFDerivAt_on_smallBall g x₀ with
    ⟨rhoSD, hrhoSD, hsourceDer⟩
  rcases exists_expAtChart_fderiv_contDiffAt_one_on_smallBall g x₀ with
    ⟨rhoSC, hrhoSC, hsourceC1⟩
  rcases
      exists_expAtChart_hasFDerivAt_on_smallBall
        (M := RoundSphere3) roundSphereMetric3 p₀ with
    ⟨rhoTD, hrhoTD, htargetDer⟩
  rcases
      exists_expAtChart_fderiv_contDiffAt_one_on_smallBall
        (M := RoundSphere3) roundSphereMetric3 p₀ with
    ⟨rhoTC, hrhoTC, htargetC1⟩
  let rhoS : ℝ := min rhoSD rhoSC
  let rhoT : ℝ := min rhoTD rhoTC
  have hrhoS : 0 < rhoS := by
    dsimp [rhoS]
    exact lt_min hrhoSD hrhoSC
  have hrhoT : 0 < rhoT := by
    dsimp [rhoT]
    exact lt_min hrhoTD hrhoTC
  refine ⟨rhoS, hrhoS, rhoT, hrhoT, ?_⟩
  intro L v hv hLv hvsrc hIso
  rcases hIso with ⟨sourceIso, hsourceIso⟩
  have hvSD : v ∈ ball (0 : E) rhoSD :=
    Metric.ball_subset_ball (min_le_left rhoSD rhoSC) hv
  have hvSC : v ∈ ball (0 : E) rhoSC :=
    Metric.ball_subset_ball (min_le_right rhoSD rhoSC) hv
  have hLvTD : L v ∈ ball (0 : E) rhoTD :=
    Metric.ball_subset_ball (min_le_left rhoTD rhoTC) hLv
  have hLvTC : L v ∈ ball (0 : E) rhoTC :=
    Metric.ball_subset_ball (min_le_right rhoTD rhoTC) hLv
  apply
    ExpChartC2.cartanChartMap_contDiffAt_two_of_expChart_derivative_fields
      (g := g) (x0 := x₀) (p0 := p₀) (L := L) (v := v)
      hvsrc
      (sourceD := fun q : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q)
      (targetD := fun q : E =>
        fderiv ℝ
          (expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) q)
      (sourceIso := sourceIso)
  · exact
      ⟨ball (0 : E) rhoSD, Metric.isOpen_ball.mem_nhds hvSD,
        fun q hq => hsourceDer q hq⟩
  · exact hsourceC1 v hvSC
  · exact hsourceIso
  · exact
      ⟨ball (0 : E) rhoTD, Metric.isOpen_ball.mem_nhds hLvTD,
        fun q hq => htargetDer q hq⟩
  · exact htargetC1 (L v) hLvTC

/--
One fixed-anchor punctured normal ball supplies the Cartan-map C2 package for
every tangent alignment.  The proof intersects the common differential-field
radius with fixed source/target regularity and chart-domain radii, shrinking
the target requirements once by a uniform operator-norm bound.
-/
theorem exists_uniform_cartanChartMap_contDiffAt_two_on_punctured_ball
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
              expAtChartOpenPartialHomeomorph (g := g) x₀
            let eS :=
              expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) p₀
            let F := CartanDifferential.cartanChartMap g x₀ p₀ L
            v ∈ eM.source ∧
              L v ∈ eS.source ∧
              eM v ∈ (extChartAt I x₀).target ∧
              eS (L v) ∈ (extChartAt I p₀).target ∧
              HasStrictFDerivAt eM (Afield v : E →L[ℝ] E) v ∧
              ContDiffAt ℝ 2 F (eM v) := by
  rcases
      UniformTangentAlignmentDifferentialField.exists_uniform_cartanChartDifferential_field_on_punctured_ball
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) with
    ⟨rhoD, hrhoD, hfields⟩
  rcases
      exists_uniform_cartanChartMap_contDiffAt_two_on_small_normal_balls
        (g := g) (x₀ := x₀) (p₀ := p₀) with
    ⟨rhoS, hrhoS, rhoT, hrhoT, hC2⟩
  rcases expAt_mem_source_of_norm_lt (g := g) (x₀ := x₀) with
    ⟨rhoMS, hrhoMS, hsourceChart⟩
  rcases
      exists_expAtChartOpenPartialHomeomorph_mem_source_of_norm_lt
        (g := g) (x₀ := x₀) with
    ⟨rhoPS, hrhoPS, hsourcePartial⟩
  rcases
      exists_expAtChartOpenPartialHomeomorph_mem_source_of_norm_lt
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨rhoPT, hrhoPT, htargetPartial⟩
  rcases
      expAt_mem_source_of_norm_lt
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨rhoMT, hrhoMT, htargetChart⟩
  rcases
      CartanMap.exists_pos_uniform_tangentAlignment_operatorNorm_bound
        g x₀ p₀ with
    ⟨C, hC_pos, hC⟩
  let rhoSource : ℝ := min rhoD (min rhoS (min rhoPS rhoMS))
  let rhoTarget : ℝ := min rhoT (min rhoPT rhoMT)
  let rho : ℝ := min rhoSource (rhoTarget / C)
  have hrhoSource : 0 < rhoSource := by
    dsimp [rhoSource]
    exact lt_min hrhoD (lt_min hrhoS (lt_min hrhoPS hrhoMS))
  have hrhoTarget : 0 < rhoTarget := by
    dsimp [rhoTarget]
    exact lt_min hrhoT (lt_min hrhoPT hrhoMT)
  have hrho : 0 < rho := by
    dsimp [rho]
    exact lt_min hrhoSource (div_pos hrhoTarget hC_pos)
  refine ⟨rho, hrho, ?_⟩
  intro L
  rcases hfields L with
    ⟨Afield, Bfield, DF, hDF, hdiff⟩
  refine ⟨Afield, Bfield, DF, hDF, ?_⟩
  intro v hv hvne
  dsimp only
  have hvSource : ‖v‖ < rhoSource :=
    hv.trans_le (min_le_left rhoSource (rhoTarget / C))
  have hvD : ‖v‖ < rhoD :=
    hvSource.trans_le (min_le_left rhoD (min rhoS (min rhoPS rhoMS)))
  have hvS : ‖v‖ < rhoS :=
    hvSource.trans_le
      ((min_le_right rhoD (min rhoS (min rhoPS rhoMS))).trans
        (min_le_left rhoS (min rhoPS rhoMS)))
  have hvPS : ‖v‖ < rhoPS :=
    hvSource.trans_le
      (((min_le_right rhoD (min rhoS (min rhoPS rhoMS))).trans
        (min_le_right rhoS (min rhoPS rhoMS))).trans
          (min_le_left rhoPS rhoMS))
  have hvMS : ‖v‖ < rhoMS :=
    hvSource.trans_le
      (((min_le_right rhoD (min rhoS (min rhoPS rhoMS))).trans
        (min_le_right rhoS (min rhoPS rhoMS))).trans
          (min_le_right rhoPS rhoMS))
  have hvTarget : ‖v‖ < rhoTarget / C :=
    hv.trans_le (min_le_right rhoSource (rhoTarget / C))
  have hLvTarget : ‖L v‖ < rhoTarget := by
    have hnorm :
        ‖L v‖ ≤
          ‖L.toContinuousLinearEquiv.toContinuousLinearMap‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (L.toContinuousLinearEquiv : E →L[ℝ] E) v
    have hnormC :
        ‖L.toContinuousLinearEquiv.toContinuousLinearMap‖ * ‖v‖ ≤
          C * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hC L) (norm_nonneg v)
    have hmul : C * ‖v‖ < rhoTarget := by
      calc
        C * ‖v‖ < C * (rhoTarget / C) :=
          mul_lt_mul_of_pos_left hvTarget hC_pos
        _ = rhoTarget := by field_simp [ne_of_gt hC_pos]
    exact hnorm.trans_lt (hnormC.trans_lt hmul)
  have hLv : ‖L v‖ < rhoT :=
    hLvTarget.trans_le (min_le_left rhoT (min rhoPT rhoMT))
  have hLvPT : ‖L v‖ < rhoPT :=
    hLvTarget.trans_le
      ((min_le_right rhoT (min rhoPT rhoMT)).trans
        (min_le_left rhoPT rhoMT))
  have hLvMT : ‖L v‖ < rhoMT :=
    hLvTarget.trans_le
      ((min_le_right rhoT (min rhoPT rhoMT)).trans
        (min_le_right rhoPT rhoMT))
  have hvsrc :
      v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source :=
    hsourcePartial v hvPS
  have hLvsrc :
      L v ∈
        (expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀).source :=
    htargetPartial (L v) hLvPT
  rcases hdiff v hvD hvne with
    ⟨hsourceStrict, _htargetStrict, _hDFinv, _hFstrict, _hpullback⟩
  have hvS_ball : v ∈ ball (0 : E) rhoS := by
    simpa [mem_ball, dist_eq_norm] using hvS
  have hLv_ball : L v ∈ ball (0 : E) rhoT := by
    simpa [mem_ball, dist_eq_norm] using hLv
  have heM_chart :
      (expAtChartOpenPartialHomeomorph (g := g) x₀) v ∈
        (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (hsourceChart v hvMS)
  have heS_chart :
      (expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v) ∈
        (extChartAt I p₀).target :=
    (extChartAt I p₀).map_source (htargetChart (L v) hLvMT)
  have hF_C2 :=
    hC2 L v hvS_ball hLv_ball hvsrc
      ⟨Afield v, hsourceStrict.hasFDerivAt⟩
  exact
    ⟨hvsrc, hLvsrc, heM_chart, heS_chart, hsourceStrict, hF_C2⟩

end UniformTangentAlignmentC2
end Poincare
