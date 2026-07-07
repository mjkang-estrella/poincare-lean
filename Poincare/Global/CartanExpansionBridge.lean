import Poincare.Global.CartanLocalIsometry
import Poincare.Global.RoundSphereCurvature

/-!
# Corrected Cartan endpoint expansion bridge

The sanity check for the bilinear endpoint expansion is decisive: in the
stereographic chart of the round sphere, the endpoint chart metric is not the
anchor chart metric away from the anchor.  It is the anchor Euclidean pairing
multiplied by the endpoint conformal factor

`16 / (‖z‖² + 4)²`.

Accordingly, this file records the corrected weighted endpoint form.  The
Cartan pullback only needs source and target endpoint expansions to carry the
same scalar endpoint chart-weight; that scalar cancels in the tangent-alignment
pairing.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanExpansionBridge

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/-- Scalar form of the stereographic conformal factor, used for the pinning check. -/
def stereographicScalarConformalFactor (r : ℝ) : ℝ :=
  16 / (r ^ 2 + 4) ^ 2

@[simp]
theorem stereographicScalarConformalFactor_zero :
    stereographicScalarConformalFactor 0 = 1 := by
  norm_num [stereographicScalarConformalFactor]

/-- At a nonzero endpoint with stereographic radius `2`, the chart weight is `1/4`. -/
theorem stereographicScalarConformalFactor_two :
    stereographicScalarConformalFactor 2 = (1 / 4 : ℝ) := by
  norm_num [stereographicScalarConformalFactor]

/--
The unweighted endpoint identity would force the endpoint conformal factor to
be `1`; the radius-`2` round-sphere endpoint gives the concrete obstruction.
-/
theorem stereographicScalarConformalFactor_two_ne_one :
    stereographicScalarConformalFactor 2 ≠ 1 := by
  norm_num [stereographicScalarConformalFactor]

/--
Polarization bridge from directional/quadratic endpoint facts to a full
bilinear identity for symmetric continuous bilinear forms.
-/
theorem bilinear_eq_of_forall_self_eq
    (B C : E →L[ℝ] E →L[ℝ] ℝ)
    (hBsymm : ∀ x y : E, B x y = B y x)
    (hCsymm : ∀ x y : E, C x y = C y x)
    (hquad : ∀ x : E, B x x = C x x) :
    ∀ x y : E, B x y = C x y := by
  intro x y
  have hxy := hquad (x + y)
  have hx := hquad x
  have hy := hquad y
  have hB :
      B (x + y) (x + y) = B x x + B y y + 2 * B x y := by
    calc
      B (x + y) (x + y) =
          B x x + B y x + (B x y + B y y) := by
            simp only [map_add, ContinuousLinearMap.add_apply]
      _ = B x x + B y y + 2 * B x y := by
            rw [hBsymm y x]
            ring
  have hC :
      C (x + y) (x + y) = C x x + C y y + 2 * C x y := by
    calc
      C (x + y) (x + y) =
          C x x + C y x + (C x y + C y y) := by
            simp only [map_add, ContinuousLinearMap.add_apply]
      _ = C x x + C y y + 2 * C x y := by
            rw [hCsymm y x]
            ring
  rw [hB, hC, hx, hy] at hxy
  nlinarith

/--
Endpoint chart-weight for the round-sphere chart, normalized relative to the
same chart's anchor coefficient.  The ratio form avoids depending on a separate
lemma that the anchor coordinate is syntactically `0`.
-/
def roundSphereEndpointChartWeight (p₀ : RoundSphere3) (z : E) : ℝ :=
  stereoInvFunAuxConformalFactor z /
    stereoInvFunAuxConformalFactor (extChartAt I p₀ p₀)

/--
Pinned corrected round-sphere endpoint metric identity: the endpoint chart
metric equals the target anchor chart metric multiplied by the endpoint
stereographic chart-weight.
-/
theorem roundSphere_chartMetric_eq_endpointWeight_mul_targetAnchor
    (p₀ : RoundSphere3) (z u w : E) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z u w =
      roundSphereEndpointChartWeight p₀ z *
        CartanMap.targetAnchorChartMetric p₀ u w := by
  have hz := roundSphereMetric3_chartMetric_eq p₀ z u w
  have hanchor :=
    roundSphereMetric3_chartMetric_eq p₀ (extChartAt I p₀ p₀) u w
  have hden :
      stereoInvFunAuxConformalFactor (extChartAt I p₀ p₀) ≠ 0 := by
    dsimp [stereoInvFunAuxConformalFactor]
    positivity
  rw [hz]
  unfold roundSphereEndpointChartWeight CartanMap.targetAnchorChartMetric
  rw [hanchor]
  field_simp [hden]

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
The target side of the corrected endpoint expansion is unconditional for the
bundled round sphere: it is exactly the pinned conformal-weight identity.
-/
theorem roundSphere_targetWeightedEndpointExpansion
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E) :
    CartanLocalIsometry.WeightedTargetEndpointExpansion L v
      (roundSphereEndpointChartWeight p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))) where
  metric := by
    intro u u'
    exact
      roundSphere_chartMetric_eq_endpointWeight_mul_targetAnchor p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u)
        (CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u')

/--
Both-side corrected endpoint bundle once the source side is proved with the
same round-sphere endpoint chart-weight.
-/
theorem weightedEndpointExpansionBundle_of_sourceExpansion_and_roundSphere
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E)
    (hsource :
      CartanLocalIsometry.WeightedSourceEndpointExpansion g x₀ v
        (roundSphereEndpointChartWeight p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v)))) :
    CartanLocalIsometry.WeightedEndpointExpansionBundle L v
      (roundSphereEndpointChartWeight p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))) where
  sourceExpansion := hsource
  targetExpansion := roundSphere_targetWeightedEndpointExpansion L v

/--
Punctured restatement of the round-sphere target expansion.  The proof still
comes from the unconditional conformal-weight identity.
-/
theorem roundSphere_targetPuncturedWeightedEndpointExpansion
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    CartanLocalIsometry.PuncturedWeightedTargetEndpointExpansion L
      (fun v : E =>
        roundSphereEndpointChartWeight p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))) where
  metric := by
    intro v _hvne u u'
    exact (roundSphere_targetWeightedEndpointExpansion L v).metric u u'

/--
Both-side punctured corrected endpoint bundle once the source side is proved on
the punctured normal-coordinate domain with the same round-sphere endpoint
chart weight.
-/
theorem puncturedWeightedEndpointExpansionBundle_of_sourceExpansion_and_roundSphere
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (hsource :
      CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀
        (fun v : E =>
          roundSphereEndpointChartWeight p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v)))) :
    CartanLocalIsometry.PuncturedWeightedEndpointExpansionBundle L
      (fun v : E =>
        roundSphereEndpointChartWeight p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))) where
  sourceExpansion := hsource
  targetExpansion := roundSphere_targetPuncturedWeightedEndpointExpansion L

/--
Corrected-form Cartan local-isometry consumer: after the source endpoint
expansion is proved with the pinned round-sphere endpoint weight, the target
side is instantiated unconditionally and the weighted pullback identity applies.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_sourceExpansion_and_roundSphere
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v))
    (u u' : E)
    (hDu :
      CartanLocalIsometry.cartanChartDifferential L A B u =
        CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u)
    (hDu' :
      CartanLocalIsometry.cartanChartDifferential L A B u' =
        CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u')
    (hsourceExpansion :
      CartanLocalIsometry.WeightedSourceEndpointExpansion g x₀ v
        (roundSphereEndpointChartWeight p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v)))) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (CartanLocalIsometry.cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (CartanLocalIsometry.cartanChartDifferential L A B u)
          (CartanLocalIsometry.cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' :=
  CartanLocalIsometry.cartanMap_isLocalIsometry_on_normalBall_of_weightedEndpointExpansionBundle
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    hvsrc hsourceDeriv htargetDeriv u u' hDu hDu'
    (weightedEndpointExpansionBundle_of_sourceExpansion_and_roundSphere
      (g := g) (x₀ := x₀) (p₀ := p₀) L v hsourceExpansion)

/--
Corrected-form nonzero Cartan local-isometry consumer from the punctured source
expansion.  The anchor case is handled separately in `CartanPunctured`.
-/
theorem cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceExpansion_and_roundSphere
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hvne : v ≠ 0)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v))
    (u u' : E)
    (hDu :
      CartanLocalIsometry.cartanChartDifferential L A B u =
        CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u)
    (hDu' :
      CartanLocalIsometry.cartanChartDifferential L A B u' =
        CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u')
    (hsourceExpansion :
      CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀
        (fun v : E =>
          roundSphereEndpointChartWeight p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v)))) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (CartanLocalIsometry.cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (CartanLocalIsometry.cartanChartDifferential L A B u)
          (CartanLocalIsometry.cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' :=
  CartanLocalIsometry.cartanMap_isLocalIsometry_on_punctured_normalBall_of_puncturedEndpointExpansionBundle
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    hvsrc hvne hsourceDeriv htargetDeriv u u' hDu hDu'
    (puncturedWeightedEndpointExpansionBundle_of_sourceExpansion_and_roundSphere
      (g := g) (x₀ := x₀) (p₀ := p₀) L hsourceExpansion)

end CartanExpansionBridge
end Poincare
