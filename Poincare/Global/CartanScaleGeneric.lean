import Poincare.Global.CartanCoefficientBridge
import Poincare.Global.CartanHomogeneity
import Poincare.Global.CartanIsometryPackage

/-!
# Hosted scale-generic Cartan bridge

This module instantiates the scale-generic coefficient bridge with the honest
hosted transverse scale coming from the small working velocity `u` and time
`T` supplied by `CartanHomogeneity`.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanScaleGeneric

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The hosted radial factor remains the ray-law factor. -/
def hostedRadialScale (_δ : ℝ) (_v : E) : ℝ := 1

/-- Working-speed scalar measured by the source anchor chart metric. -/
def hostedSourceSpeed
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (δ : ℝ) (v : E) : ℝ :=
  Real.sqrt
    (CartanMap.sourceAnchorChartMetric g x₀
      (CartanHomogeneity.workingVelocity δ v)
      (CartanHomogeneity.workingVelocity δ v))

/-- Working-speed scalar measured after alignment in the target anchor chart. -/
def hostedTargetSpeed
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) : ℝ :=
  Real.sqrt
    (CartanMap.targetAnchorChartMetric p₀
      (L (CartanHomogeneity.workingVelocity δ v))
      (L (CartanHomogeneity.workingVelocity δ v)))

/-- The sine factor at working speed `speed` and hosted time `T`. -/
def hostedTransverseScaleFromSpeed (speed T : ℝ) : ℝ :=
  Real.sin (speed * T) / (speed * T)

/-- Honest source transverse factor from the hosted `(u, T)` data. -/
def hostedSourceTransverseScale
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (δ : ℝ) (v : E) : ℝ :=
  hostedTransverseScaleFromSpeed
    (hostedSourceSpeed g x₀ δ v)
    (CartanHomogeneity.workingTime δ v)

/-- Honest target transverse factor from the aligned hosted `(u, T)` data. -/
def hostedTargetTransverseScale
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) : ℝ :=
  hostedTransverseScaleFromSpeed
    (hostedTargetSpeed L δ v)
    (CartanHomogeneity.workingTime δ v)

/--
Hosted instantiation of the scale-generic bridge.

The source blocks use the source hosted scale, while the target block and
differential identification are allowed to state the same construction through
the aligned target speed.  The proof rewrites those target scales to the
source scales using the tangent-alignment metric preservation law, then applies
the scale-generic coefficient bridge.
-/
theorem cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E} {κ : E → ℝ} (δ : ℝ)
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
          (hostedRadialScale δ v) (hostedTargetTransverseScale L δ v) v u)
    (hDu' :
      CartanLocalIsometry.cartanChartDifferential L A B u' =
        CartanLocalIsometry.targetScaledNormalVector L
          (hostedRadialScale δ v) (hostedTargetTransverseScale L δ v) v u')
    (hRadialRadial :
      ∀ {v : E},
        v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source →
        v ≠ 0 →
        ∀ u u' : E,
          CovariantDerivative.chartMetric g.inner x₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
              (CartanPullback.radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u)
              (CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v u') =
            κ v *
              CartanMap.sourceAnchorChartMetric g x₀
                ((hostedRadialScale δ v) •
                  CartanPullback.radialPart
                    (CartanMap.sourceAnchorChartMetric g x₀) v u)
                ((hostedRadialScale δ v) •
                  CartanPullback.radialPart
                    (CartanMap.sourceAnchorChartMetric g x₀) v u'))
    (hRadialTransverse :
      ∀ {v : E},
        v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source →
        v ≠ 0 →
        ∀ u u' : E,
          CovariantDerivative.chartMetric g.inner x₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
              (CartanPullback.radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u)
              (CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u') = 0)
    (hTransverseTransverse :
      ∀ {v : E},
        v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source →
        v ≠ 0 →
        ∀ u u' : E,
          CovariantDerivative.chartMetric g.inner x₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
              (CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u)
              (CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u') =
            κ v *
              CartanMap.sourceAnchorChartMetric g x₀
                ((hostedSourceTransverseScale g x₀ δ v) •
                  CartanPullback.transversePart
                    (CartanMap.sourceAnchorChartMetric g x₀) v u)
                ((hostedSourceTransverseScale g x₀ δ v) •
                  CartanPullback.transversePart
                    (CartanMap.sourceAnchorChartMetric g x₀) v u'))
    (hTargetMetric :
      ∀ {v : E}, v ≠ 0 →
        ∀ u u' : E,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) p₀) (L v))
              (CartanLocalIsometry.targetScaledNormalVector L
                (hostedRadialScale δ v) (hostedTargetTransverseScale L δ v) v u)
              (CartanLocalIsometry.targetScaledNormalVector L
                (hostedRadialScale δ v) (hostedTargetTransverseScale L δ v) v u') =
            κ v *
              CartanMap.targetAnchorChartMetric p₀
                (CartanLocalIsometry.targetScaledNormalVector L
                  (hostedRadialScale δ v) (hostedTargetTransverseScale L δ v) v u)
                (CartanLocalIsometry.targetScaledNormalVector L
                  (hostedRadialScale δ v) (hostedTargetTransverseScale L δ v) v u')) :
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
  have hσ :
      ∀ w : E,
        hostedTargetTransverseScale L δ w =
          hostedSourceTransverseScale g x₀ δ w := by
    intro w
    simp [hostedTargetTransverseScale, hostedSourceTransverseScale,
      hostedTargetSpeed, hostedSourceSpeed, CartanMap.TangentAlignment.map_app]
  have hDuSource :
      CartanLocalIsometry.cartanChartDifferential L A B u =
        CartanLocalIsometry.targetScaledNormalVector L
          (hostedRadialScale δ v) (hostedSourceTransverseScale g x₀ δ v) v u := by
    simpa [hσ v] using hDu
  have hDuSource' :
      CartanLocalIsometry.cartanChartDifferential L A B u' =
        CartanLocalIsometry.targetScaledNormalVector L
          (hostedRadialScale δ v) (hostedSourceTransverseScale g x₀ δ v) v u' := by
    simpa [hσ v] using hDu'
  have hTargetMetricSource :
      ∀ {w : E}, w ≠ 0 →
        ∀ a b : E,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) p₀) (L w))
              (CartanLocalIsometry.targetScaledNormalVector L
                (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w a)
              (CartanLocalIsometry.targetScaledNormalVector L
                (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w b) =
            κ w *
              CartanMap.targetAnchorChartMetric p₀
                (CartanLocalIsometry.targetScaledNormalVector L
                  (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w a)
                (CartanLocalIsometry.targetScaledNormalVector L
                  (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w b) := by
    intro w hw a b
    simpa [hσ w] using hTargetMetric (v := w) hw a b
  have hAnchorPairing :
      ∀ {w : E}, w ≠ 0 →
        ∀ a b : E,
          κ w *
              CartanMap.targetAnchorChartMetric p₀
                (CartanLocalIsometry.targetScaledNormalVector L
                  (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w a)
                (CartanLocalIsometry.targetScaledNormalVector L
                  (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w b) =
            κ w *
              CartanMap.sourceAnchorChartMetric g x₀
                (CartanLocalIsometry.sourceScaledNormalVector g x₀
                  (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w a)
                (CartanLocalIsometry.sourceScaledNormalVector g x₀
                  (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w b) := by
    intro w _hw a b
    exact congrArg (fun q : ℝ => κ w * q)
      (CartanLocalIsometry.sameFactors_anchor_pair
        (g := g) (x₀ := x₀) (p₀ := p₀) L
        (hostedRadialScale δ w) (hostedSourceTransverseScale g x₀ δ w) w a b)
  exact
    Poincare.CartanCoefficientBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_scale_generic_endpoint_pairings
        (g := g) (x₀ := x₀) (p₀ := p₀) L
        (v := v) (A := A) (B := B) (κsource := κ) (κtarget := κ)
        (ρ := hostedRadialScale δ) (σ := hostedSourceTransverseScale g x₀ δ)
        hvsrc hvne hsourceDeriv htargetDeriv u u' hDuSource hDuSource'
        hRadialRadial hRadialTransverse hTransverseTransverse
        hTargetMetricSource hAnchorPairing

end CartanScaleGeneric
end Poincare
