import Poincare.Global.CartanWeightInvariant

/-!
# Cartan coefficient bridge

This module packages the source-side coefficient algebra for the punctured
Cartan route.  The geometric input is deliberately the three endpoint pairing
blocks: radial-radial, radial-transverse, and transverse-transverse.  The
proof expands arbitrary endpoint chart vectors by the existing Gram
decomposition and feeds the resulting source-owned expansion to the invariant
Cartan local-isometry consumer.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanCoefficientBridge

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Source endpoint coefficient blocks imply the punctured source-owned expansion,
and hence the Cartan chart pullback identity through the existing
weight-invariant consumer.
-/
theorem cartanMap_isLocalIsometry_on_punctured_normalBall_of_source_endpoint_pairings
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
            κsource v *
              CartanMap.sourceAnchorChartMetric g x₀
                (CartanPullback.radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u)
                (CartanPullback.radialPart
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
            κsource v *
              CartanMap.sourceAnchorChartMetric g x₀
                ((CartanLocalIsometry.transverseScale v) •
                  CartanPullback.transversePart
                    (CartanMap.sourceAnchorChartMetric g x₀) v u)
                ((CartanLocalIsometry.transverseScale v) •
                  CartanPullback.transversePart
                    (CartanMap.sourceAnchorChartMetric g x₀) v u'))
    (hpairing :
      CartanWeightInvariant.PuncturedWeightedAnchorPairing L κsource
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
          u u' := by
  let hsourceExpansion :
      CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀ κsource := by
    refine ⟨?_⟩
    intro v hvsrc hvne u u'
    let G : E →L[ℝ] E →L[ℝ] ℝ :=
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    let S : E →L[ℝ] E →L[ℝ] ℝ := CartanMap.sourceAnchorChartMetric g x₀
    let r : E := CartanPullback.radialPart S v u
    let t : E := CartanPullback.transversePart S v u
    let r' : E := CartanPullback.radialPart S v u'
    let t' : E := CartanPullback.transversePart S v u'
    let σ : ℝ := CartanLocalIsometry.transverseScale v
    have hu : u = r + t := by
      show u =
        CartanPullback.radialPart S v u + CartanPullback.transversePart S v u
      rw [CartanPullback.radialPart_add_transversePart]
    have hu' : u' = r' + t' := by
      show u' =
        CartanPullback.radialPart S v u' + CartanPullback.transversePart S v u'
      rw [CartanPullback.radialPart_add_transversePart]
    have hrr : G r r' = κsource v * S r r' := by
      simpa [G, S, r, r'] using hRadialRadial hvsrc hvne u u'
    have hrt : G r t' = 0 := by
      simpa [G, S, r, t'] using hRadialTransverse hvsrc hvne u u'
    have htr : G t r' = 0 := by
      have hsymm :
          G t r' = G r' t := by
        simpa [G] using
          (CovariantDerivative.chartMetric_symm g.inner
            (fun y a b => g.symm y a b) x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            t r')
      have hzero : G r' t = 0 := by
        simpa [G, S, r', t] using hRadialTransverse hvsrc hvne u' u
      exact hsymm.trans hzero
    have htt : G t t' = κsource v * S (σ • t) (σ • t') := by
      simpa [G, S, t, t', σ] using hTransverseTransverse hvsrc hvne u u'
    have hSrt' : S r (σ • t') = 0 := by
      simp [r, t', S, CartanPullback.radialPart_transversePart_pair
        (B := S) (v := v) (u := u) (u' := u')
        (CartanMap.sourceAnchorChartMetric_symm g x₀)
        (CartanPullback.sourceAnchorChartMetric_self_ne_zero
          (g := g) (x₀ := x₀) hvne)]
    have hStr' : S (σ • t) r' = 0 := by
      simp [r', t, S, CartanPullback.transversePart_radialPart_pair
        (B := S) (v := v) (u := u) (u' := u')
        (CartanPullback.sourceAnchorChartMetric_self_ne_zero
          (g := g) (x₀ := x₀) hvne)]
    have hSscaled :
        S (r + σ • t) (r' + σ • t') =
          S r r' + S (σ • t) (σ • t') := by
      simp only [map_add, ContinuousLinearMap.add_apply, hSrt', hStr',
        zero_add, add_zero]
    calc
      G u u' = G (r + t) (r' + t') := by rw [hu, hu']
      _ = G r r' + G r t' + G t r' + G t t' := by
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      _ = κsource v * S r r' + 0 + 0 + κsource v * S (σ • t) (σ • t') := by
        rw [hrr, hrt, htr, htt]
      _ = κsource v * (S r r' + S (σ • t) (σ • t')) := by ring
      _ = κsource v * S (r + σ • t) (r' + σ • t') := by rw [hSscaled]
      _ =
          κsource v *
            CartanMap.sourceAnchorChartMetric g x₀
              (CartanLocalIsometry.sourceScaledNormalVector g x₀
                1 (CartanLocalIsometry.transverseScale v) v u)
              (CartanLocalIsometry.sourceScaledNormalVector g x₀
                1 (CartanLocalIsometry.transverseScale v) v u') := by
        simp [CartanLocalIsometry.sourceScaledNormalVector, S, r, t, r', t', σ]
  exact
    CartanWeightInvariant.cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceOwned_and_roundSphere
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      hvsrc hvne hsourceDeriv htargetDeriv u u' hDu hDu'
      hsourceExpansion hpairing

end CartanCoefficientBridge
end Poincare
