import Poincare.Global.CartanFinalComposition
import Poincare.Global.PairingFeed

/-!
# Hosted endpoint equality chain

This module isolates the algebraic endpoint-pairing chain used by the final
Cartan local-isometry route.  Once the source and target hosted Jacobi
endpoint pairings have both been pinned to the same `sin²` scalar times their
anchor chart metrics, the tangent alignment identifies the anchor pairings.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace EqualityChain

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The hosted source and target speeds agree after applying the tangent alignment. -/
theorem hostedTargetSpeed_eq_hostedSourceSpeed
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) :
    CartanScaleGeneric.hostedTargetSpeed L δ v =
      CartanScaleGeneric.hostedSourceSpeed g x₀ δ v := by
  simp [CartanScaleGeneric.hostedTargetSpeed, CartanScaleGeneric.hostedSourceSpeed,
    CartanMap.TangentAlignment.map_app]

/-- Consequently the hosted transverse sine scales agree through the alignment. -/
theorem hostedTargetTransverseScale_eq_hostedSourceTransverseScale
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) :
    CartanScaleGeneric.hostedTargetTransverseScale L δ v =
      CartanScaleGeneric.hostedSourceTransverseScale g x₀ δ v := by
  simp [CartanScaleGeneric.hostedTargetTransverseScale,
    CartanScaleGeneric.hostedSourceTransverseScale,
    hostedTargetSpeed_eq_hostedSourceSpeed (g := g) (x₀ := x₀) (p₀ := p₀) L δ v]

/-- The hosted `sin²` factors agree because the aligned hosted speeds agree. -/
theorem hosted_sin_sq_factor_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) :
    Real.sin
          (CartanScaleGeneric.hostedTargetSpeed L δ v *
            CartanHomogeneity.workingTime δ v) ^ 2 =
      Real.sin
          (CartanScaleGeneric.hostedSourceSpeed g x₀ δ v *
            CartanHomogeneity.workingTime δ v) ^ 2 := by
  rw [hostedTargetSpeed_eq_hostedSourceSpeed (g := g) (x₀ := x₀) (p₀ := p₀) L δ v]

/--
The verbatim hosted endpoint-pairing feed follows from the two pinned
`sin²` endpoint-pairing formulas and equality of the two sine factors.
-/
theorem hosted_endpoint_pairing_feed_of_sin_sq_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {Ψs Ψt : E → ℝ → E × E} {Ts Tt θs θt : ℝ}
    (hSin : Real.sin θt ^ 2 = Real.sin θs ^ 2)
    (hSourcePinned :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a Ts).1 (Ψs a' Ts).1 =
          Real.sin θs ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPinned :
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
          Real.sin θt ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')) :
    ∀ a a' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a Ts).1 (Ψs a' Ts).1 := by
  intro a a'
  calc
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
      Real.sin θt ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') :=
        hTargetPinned a a'
    _ = Real.sin θs ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') := by
        rw [hSin]
    _ = Real.sin θs ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a' := by
        rw [CartanMap.TangentAlignment.map_app L a a']
    _ =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        (Ψs a Ts).1 (Ψs a' Ts).1 := (hSourcePinned a a').symm

/-- Common-angle specialization of the hosted endpoint-pairing equality chain. -/
theorem hosted_endpoint_pairing_feed_of_common_sin_sq_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {Ψs Ψt : E → ℝ → E × E} {Ts Tt θ : ℝ}
    (hSourcePinned :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a Ts).1 (Ψs a' Ts).1 =
          Real.sin θ ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPinned :
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
          Real.sin θ ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')) :
    ∀ a a' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a Ts).1 (Ψs a' Ts).1 :=
  hosted_endpoint_pairing_feed_of_sin_sq_anchor_pairings
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (Ψs := Ψs) (Ψt := Ψt) (Ts := Ts) (Tt := Tt)
    (θs := θ) (θt := θ) rfl hSourcePinned hTargetPinned

/--
Local-isometry consumer with the hosted endpoint feed discharged by the
same-`sin²` equality chain.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    {Ψs Ψt : E → ℝ → E × E} {Ts Tt θs θt : ℝ}
    {hadds : ∀ w w' : E,
      (Ψs (w + w') Ts).1 = (Ψs w Ts).1 + (Ψs w' Ts).1}
    {hsmuls : ∀ (c : ℝ) (w : E),
      (Ψs (c • w) Ts).1 = c • (Ψs w Ts).1}
    {haddt : ∀ w w' : E,
      (Ψt (w + w') Tt).1 = (Ψt w Tt).1 + (Ψt w' Tt).1}
    {hsmult : ∀ (c : ℝ) (w : E),
      (Ψt (c • w) Tt).1 = c • (Ψt w Tt).1}
    (hA :
      (A : E →L[ℝ] E) =
        linearizedEndpointCLM (Ψ := Ψs) Ts hadds hsmuls)
    (hB :
      (B : E →L[ℝ] E) =
        linearizedEndpointCLM (Ψ := Ψt) Tt haddt hsmult)
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
    (hSin : Real.sin θt ^ 2 = Real.sin θs ^ 2)
    (hSourcePinned :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a Ts).1 (Ψs a' Ts).1 =
          Real.sin θs ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPinned :
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
          Real.sin θt ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')) :
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
  PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (A := A) (B := B) (Ψs := Ψs) (Ψt := Ψt)
    (Ts := Ts) (Tt := Tt)
    hA hB hvsrc hsourceDeriv htargetDeriv u u'
    (hosted_endpoint_pairing_feed_of_sin_sq_anchor_pairings
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (Ψs := Ψs) (Ψt := Ψt) (Ts := Ts) (Tt := Tt)
      hSin hSourcePinned hTargetPinned)

end EqualityChain
end Poincare
