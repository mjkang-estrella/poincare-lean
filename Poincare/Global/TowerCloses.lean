import Poincare.Global.FieldProducer
import Poincare.Global.PackageLands

/-!
# Produced derivative fields feed the F-transition tower

This module threads the currently exported producer through the existing
F-transition consumer.  The produced source and target derivative fields are
genuine local derivative fields; the only remaining chart-side inputs are their
`C1` dependence, the invertible source derivative used by the inverse-function
handoff, and the metric derivative hypotheses already present in the
F-transition interface.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace TowerCloses

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The produced exponential-chart derivative fields feed the existing
`FieldProducer -> ExpChartC2 -> ContDiffTwo -> EndpointBridge -> FTransitionDone`
assembly.

The statement exposes the actual selected fields and their neighborhood
`HasFDerivAt` facts from `FieldProducer`.  Supplying `ContDiffAt ℝ 1` for those
same selected fields closes the current consumer chain and yields the signed
Christoffel F-transition law on a common punctured ball.
-/
theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_derivative_fields_c1
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
            ∀ {sourceIso : E3 ≃L[ℝ] E3},
              ContDiffAt ℝ 1 sourceD v →
              HasFDerivAt eM (sourceIso : E3 →L[ℝ] E3) v →
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
      FieldProducer.exists_source_target_expChart_derivative_fields_on_aligned_ball
        (g := g) (x₀ := x0) (p₀ := p0) L with
    ⟨ρprod, hρprod_pos, sourceD, targetD, hfields⟩
  rcases
      PackageLands.exists_cartanChartMap_christoffelAt_F_transition_law_of_expChart_derivative_fields
        (g := g) hcurv (x0 := x0) (p0 := p0) L with
    ⟨ρtrans, hρtrans_pos, Afield, Bfield, DF, hDF_def, htransition⟩
  use min ρprod ρtrans, lt_min hρprod_pos hρtrans_pos,
    sourceD, targetD, Afield, Bfield, DF
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
  have hvprod : ‖v‖ < ρprod := lt_of_lt_of_le hv (min_le_left _ _)
  have hvtrans : ‖v‖ < ρtrans := lt_of_lt_of_le hv (min_le_right _ _)
  rcases hfields v hvprod with
    ⟨hvsrc, hvtgt, hsource_at, htarget_at, hsource_near, htarget_near⟩
  exact
    ⟨hvsrc, hvtgt, hsource_at, htarget_at, hsource_near, htarget_near, by
      intro sourceIso hsourceD_c1 hsourceIso_deriv htargetD_c1 hG₀ hG₁
        b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w
      exact
        htransition v hvtrans hvne hvsrc
          (sourceD := sourceD) (targetD := targetD) (sourceIso := sourceIso)
          hsource_near hsourceD_c1 hsourceIso_deriv htarget_near
          htargetD_c1 hG₀ hG₁ b₀ b₁ hb₀ hb₁ hb₀G hb₁G u w⟩

end TowerCloses
end Poincare
