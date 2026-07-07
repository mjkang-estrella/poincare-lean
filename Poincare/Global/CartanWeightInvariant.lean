import Poincare.Global.CoefficientEvolution
import Poincare.Global.CartanPunctured

/-!
# Chart-owned Cartan endpoint weights

This module pins the chart-dependence issue left open by `M5-rigid-20`.

The round-sphere scalar
`CoefficientEvolution.roundSpherePinnedWeight t = cos (t / 2) ^ 4` is a
statement about the sphere's stereographic chart.  It cannot be imposed as the
source coefficient for an arbitrary source atlas chart.  Even the elementary
linear chart rescaling `z ↦ 2 z` changes raw chart coefficients by `1 / 4` at
the anchor while leaving the underlying geometry unchanged.  Therefore the
source-side expansion must own its own endpoint weight, and the Cartan
consumer must use a symmetric weighted anchor pairing rather than identifying
the source weight with the target chart's weight.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanWeightInvariant

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/--
Toy scalar model for a chart rescaling `z ↦ c z`: raw metric coefficients in
the rescaled coordinate vector basis are multiplied by `1 / c^2`.
-/
def chartRescaledAbsoluteCoefficient (c t : ℝ) : ℝ :=
  (1 / c ^ 2) * CoefficientEvolution.roundSpherePinnedWeight t

@[simp]
theorem roundSpherePinnedWeight_zero :
    CoefficientEvolution.roundSpherePinnedWeight 0 = 1 := by
  norm_num [CoefficientEvolution.roundSpherePinnedWeight]

/--
Concrete pin verdict: the raw coefficient in the rescaled chart at the anchor
is `1 / 4`, not the sphere chart's pinned value `1`.
-/
theorem chartRescaledAbsoluteCoefficient_two_zero_ne_pinned :
    chartRescaledAbsoluteCoefficient 2 0 ≠
      CoefficientEvolution.roundSpherePinnedWeight 0 := by
  norm_num [chartRescaledAbsoluteCoefficient,
    CoefficientEvolution.roundSpherePinnedWeight]

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
The symmetric weighted anchor pairing needed when the source and target
endpoint weights are chart-owned separately.  This is the ratio-invariant slot:
any Jacobian or alignment factor must be reflected here, instead of forcing
`κsource = κtarget` by chart convention.
-/
structure PuncturedWeightedAnchorPairing
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (κsource κtarget : E → ℝ) : Prop where
  pairing :
    ∀ {v : E}, v ≠ 0 →
      ∀ u u' : E,
        κtarget v *
            CartanMap.targetAnchorChartMetric p₀
              (CartanLocalIsometry.targetScaledNormalVector L
                1 (CartanLocalIsometry.transverseScale v) v u)
              (CartanLocalIsometry.targetScaledNormalVector L
                1 (CartanLocalIsometry.transverseScale v) v u') =
          κsource v *
            CartanMap.sourceAnchorChartMetric g x₀
              (CartanLocalIsometry.sourceScaledNormalVector g x₀
                1 (CartanLocalIsometry.transverseScale v) v u)
              (CartanLocalIsometry.sourceScaledNormalVector g x₀
                1 (CartanLocalIsometry.transverseScale v) v u')

/-- The previous same-weight Cartan algebra is a special case of the invariant pairing. -/
theorem puncturedWeightedAnchorPairing_of_same_weight
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (κ : E → ℝ) :
    PuncturedWeightedAnchorPairing L κ κ where
  pairing := by
    intro v _hvne u u'
    exact congrArg (fun q : ℝ => κ v * q)
      (CartanLocalIsometry.sameFactors_anchor_pair
        (g := g) (x₀ := x₀) (p₀ := p₀) L
        1 (CartanLocalIsometry.transverseScale v) v u u')

/--
Invariant punctured endpoint bundle with a source-owned weight, a target-owned
weight, and the weighted anchor pairing that makes the final pullback
chart-independent.
-/
structure PuncturedWeightInvariantEndpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (κsource κtarget : E → ℝ) : Prop where
  sourceExpansion :
    CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀ κsource
  targetExpansion :
    CartanLocalIsometry.PuncturedWeightedTargetEndpointExpansion L κtarget
  anchorPairing :
    PuncturedWeightedAnchorPairing L κsource κtarget

/-- Package the true source-owned punctured expansion once its metric identity is supplied. -/
theorem puncturedSourceOwnedEndpointExpansion_of_metric_identity
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (κsource : E → ℝ)
    (hmetric :
      ∀ {v : E},
        v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source →
        v ≠ 0 →
        ∀ u u' : E,
          CovariantDerivative.chartMetric g.inner x₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
              u u' =
            κsource v *
              CartanMap.sourceAnchorChartMetric g x₀
                (CartanLocalIsometry.sourceScaledNormalVector g x₀
                  1 (CartanLocalIsometry.transverseScale v) v u)
                (CartanLocalIsometry.sourceScaledNormalVector g x₀
                  1 (CartanLocalIsometry.transverseScale v) v u')) :
    CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀ κsource where
  metric := hmetric

/-- The existing same-weight punctured bundle embeds in the invariant bundle. -/
theorem puncturedWeightInvariantEndpointExpansionBundle_of_same_weight
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (κ : E → ℝ)
    (hexpansion : CartanLocalIsometry.PuncturedWeightedEndpointExpansionBundle L κ) :
    PuncturedWeightInvariantEndpointExpansionBundle L κ κ where
  sourceExpansion := hexpansion.sourceExpansion
  targetExpansion := hexpansion.targetExpansion
  anchorPairing := puncturedWeightedAnchorPairing_of_same_weight L κ

/--
Round-sphere target side plus a source-owned expansion.  The source weight is
not identified with the target stereographic weight; the required comparison is
the explicit weighted anchor pairing.
-/
theorem puncturedWeightInvariantEndpointExpansionBundle_of_sourceOwned_and_roundSphere
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (κsource : E → ℝ)
    (hsource :
      CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀ κsource)
    (hpairing :
      PuncturedWeightedAnchorPairing L κsource
        (fun v : E =>
          CartanExpansionBridge.roundSphereEndpointChartWeight p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v)))) :
    PuncturedWeightInvariantEndpointExpansionBundle L κsource
      (fun v : E =>
        CartanExpansionBridge.roundSphereEndpointChartWeight p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))) where
  sourceExpansion := hsource
  targetExpansion :=
    CartanExpansionBridge.roundSphere_targetPuncturedWeightedEndpointExpansion L
  anchorPairing := hpairing

/--
Pointwise pullback identity from the invariant bundle.  The two chart-owned
weights cancel through `anchorPairing`; no source chart is forced to use the
sphere chart's scalar.
-/
theorem cartanMap_chart_pullback_identity_of_weightInvariantEndpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hvne : v ≠ 0) (u u' : E) {κsource κtarget : E → ℝ}
    (hexpansion :
      PuncturedWeightInvariantEndpointExpansionBundle L κsource κtarget) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u)
        (CartanLocalIsometry.targetScaledNormalVector L
          1 (CartanLocalIsometry.transverseScale v) v u') =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        u u' := by
  have htarget := hexpansion.targetExpansion.metric hvne u u'
  have hsource := hexpansion.sourceExpansion.metric hvsrc hvne u u'
  have hpairing := hexpansion.anchorPairing.pairing hvne u u'
  rw [htarget, hsource]
  exact hpairing

/--
Nonzero Cartan local-isometry consumer for the invariant source-owned bundle.
-/
theorem cartanMap_isLocalIsometry_on_punctured_normalBall_of_weightInvariantEndpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E} {κsource κtarget : E → ℝ}
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
    (hexpansion :
      PuncturedWeightInvariantEndpointExpansionBundle L κsource κtarget) :
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
          u u' := by
  constructor
  · simpa [CartanLocalIsometry.cartanChartDifferential] using
      CartanDifferential.cartanChartMap_hasStrictFDerivAt_of_expAtChart
        (g := g) (x₀ := x₀) (p₀ := p₀) (L := L)
        (v := v) (A := A) (B := B)
        hvsrc hsourceDeriv htargetDeriv
  · have hpull :=
      cartanMap_chart_pullback_identity_of_weightInvariantEndpointExpansionBundle
        (g := g) (x₀ := x₀) (p₀ := p₀) L hvsrc hvne u u' hexpansion
    simpa [hDu, hDu'] using hpull

/--
Round-sphere target consumer with a source-owned punctured weight and an
explicit weighted anchor comparison.
-/
theorem cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceOwned_and_roundSphere
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E} {κsource : E → ℝ}
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
      CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀ κsource)
    (hpairing :
      PuncturedWeightedAnchorPairing L κsource
        (fun v : E =>
          CartanExpansionBridge.roundSphereEndpointChartWeight p₀
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
  cartanMap_isLocalIsometry_on_punctured_normalBall_of_weightInvariantEndpointExpansionBundle
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    hvsrc hvne hsourceDeriv htargetDeriv u u' hDu hDu'
    (puncturedWeightInvariantEndpointExpansionBundle_of_sourceOwned_and_roundSphere
      (g := g) (x₀ := x₀) (p₀ := p₀) L κsource hsourceExpansion hpairing)

end CartanWeightInvariant
end Poincare
