import Poincare.Global.CartanCoefficientBridge
import Poincare.Global.LinearizedCLM

/-!
# Pairing route for the Cartan pullback

This module records the direct pairing bridge for the Cartan route.  The
vector-valued radial/transverse action equations are not needed for the final
pullback identity: it is enough to know the endpoint pairings of the source
and target exponential differentials on the corresponding initial directions.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace PairingRoute

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Three endpoint-pairing blocks imply the full derivative endpoint pairing.

This is the pairing-only analogue of the Gram-decomposition algebra in
`CartanCoefficientBridge`: no pointwise vector action equation for `D` is
assumed, only its three endpoint pairings on radial/radial,
radial/transverse, and transverse/transverse inputs.
-/
theorem derivative_pairing_eq_scaled_pairing_of_radial_transverse_blocks
    (G S : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E)
    (hGsymm : ∀ x y : E, G x y = G y x)
    (hSsymm : ∀ x y : E, S x y = S y x)
    {v : E} (hSvv : S v v ≠ 0) {κ ρ σ : ℝ}
    (hRadialRadial :
      ∀ u u' : E,
        G (D (CartanPullback.radialPart S v u))
          (D (CartanPullback.radialPart S v u')) =
          κ *
            S (ρ • CartanPullback.radialPart S v u)
              (ρ • CartanPullback.radialPart S v u'))
    (hRadialTransverse :
      ∀ u u' : E,
        G (D (CartanPullback.radialPart S v u))
          (D (CartanPullback.transversePart S v u')) = 0)
    (hTransverseTransverse :
      ∀ u u' : E,
        G (D (CartanPullback.transversePart S v u))
          (D (CartanPullback.transversePart S v u')) =
          κ *
            S (σ • CartanPullback.transversePart S v u)
              (σ • CartanPullback.transversePart S v u')) :
    ∀ u u' : E,
      G (D u) (D u') =
        κ *
          S (ρ • CartanPullback.radialPart S v u +
              σ • CartanPullback.transversePart S v u)
            (ρ • CartanPullback.radialPart S v u' +
              σ • CartanPullback.transversePart S v u') := by
  intro u u'
  let r : E := CartanPullback.radialPart S v u
  let t : E := CartanPullback.transversePart S v u
  let r' : E := CartanPullback.radialPart S v u'
  let t' : E := CartanPullback.transversePart S v u'
  have hu : u = r + t := by
    show u = CartanPullback.radialPart S v u + CartanPullback.transversePart S v u
    rw [CartanPullback.radialPart_add_transversePart]
  have hu' : u' = r' + t' := by
    show u' =
      CartanPullback.radialPart S v u' + CartanPullback.transversePart S v u'
    rw [CartanPullback.radialPart_add_transversePart]
  have hrr : G (D r) (D r') = κ * S (ρ • r) (ρ • r') := by
    simpa [r, r'] using hRadialRadial u u'
  have hrt : G (D r) (D t') = 0 := by
    simpa [r, t'] using hRadialTransverse u u'
  have htr : G (D t) (D r') = 0 := by
    have hsymm : G (D t) (D r') = G (D r') (D t) := hGsymm (D t) (D r')
    have hzero : G (D r') (D t) = 0 := by
      simpa [r', t] using hRadialTransverse u' u
    exact hsymm.trans hzero
  have htt : G (D t) (D t') = κ * S (σ • t) (σ • t') := by
    simpa [t, t'] using hTransverseTransverse u u'
  have hSrt' : S (ρ • r) (σ • t') = 0 := by
    simp [r, t', CartanPullback.radialPart_transversePart_pair
      (B := S) (v := v) (u := u) (u' := u') hSsymm hSvv]
  have hStr' : S (σ • t) (ρ • r') = 0 := by
    simp [r', t, CartanPullback.transversePart_radialPart_pair
      (B := S) (v := v) (u := u) (u' := u') hSvv]
  have hSscaled :
      S (ρ • r + σ • t) (ρ • r' + σ • t') =
        S (ρ • r) (ρ • r') + S (σ • t) (σ • t') := by
    simp only [map_add, ContinuousLinearMap.add_apply, hSrt', hStr',
      zero_add, add_zero]
  calc
    G (D u) (D u') = G (D (r + t)) (D (r' + t')) := by rw [hu, hu']
    _ = G (D r) (D r') + G (D r) (D t') +
        G (D t) (D r') + G (D t) (D t') := by
      simp only [map_add, ContinuousLinearMap.add_apply]
      ring
    _ = κ * S (ρ • r) (ρ • r') + 0 + 0 +
        κ * S (σ • t) (σ • t') := by
      rw [hrr, hrt, htr, htt]
    _ = κ * (S (ρ • r) (ρ • r') + S (σ • t) (σ • t')) := by ring
    _ = κ * S (ρ • r + σ • t) (ρ • r' + σ • t') := by rw [hSscaled]

/--
The endpoint pairing of a strict-derivative CLM is exactly the pairing of the
hosted linearized position values `Ψ w T`.
-/
theorem linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
    (G : E →L[ℝ] E →L[ℝ] ℝ)
    {Ψ : E → ℝ → E × E} {T : ℝ}
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (w w' : E) :
    G (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul w)
        (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul w') =
      G (Ψ w T).1 (Ψ w' T).1 := by
  simp [linearizedEndpointCLM_apply]

/--
Direct Cartan pullback from source and target derivative endpoint pairings.

For arbitrary endpoint chart vectors `u` and `u'`, write their source initial
directions as `A.symm u` and `A.symm u'`.  The source pairing computes the
metric of `u,u'`; the target pairing computes the metric of the Cartan
differential images.  The weighted anchor comparison is the only remaining
algebra needed to identify the two.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_weighted_derivative_endpoint_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E} {κsource κtarget : ℝ}
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
    (hSourcePairing :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a') =
          κsource * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPairing :
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) =
          κtarget * CartanMap.targetAnchorChartMetric p₀ (L a) (L a'))
    (hAnchorPairing :
      ∀ a a' : E,
        κtarget * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') =
          κsource * CartanMap.sourceAnchorChartMetric g x₀ a a') :
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
  · let a : E := A.symm u
    let a' : E := A.symm u'
    have hsource :
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            u u' =
          κsource * CartanMap.sourceAnchorChartMetric g x₀ a a' := by
      simpa [a, a'] using hSourcePairing a a'
    have htarget :
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (CartanLocalIsometry.cartanChartDifferential L A B u)
            (CartanLocalIsometry.cartanChartDifferential L A B u') =
          κtarget * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') := by
      simpa [CartanLocalIsometry.cartanChartDifferential, a, a'] using
        hTargetPairing a a'
    calc
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (CartanLocalIsometry.cartanChartDifferential L A B u)
          (CartanLocalIsometry.cartanChartDifferential L A B u') =
        κtarget * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') := htarget
      _ = κsource * CartanMap.sourceAnchorChartMetric g x₀ a a' :=
        hAnchorPairing a a'
      _ =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' := hsource.symm

/--
Same-weight specialization of the derivative-pairing bridge.  The weighted
anchor comparison is discharged by the tangent-alignment pairing law.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_derivative_endpoint_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E} {κ : ℝ}
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
    (hSourcePairing :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a') =
          κ * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPairing :
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) =
          κ * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')) :
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
  cartanMap_isLocalIsometry_on_normalBall_of_weighted_derivative_endpoint_pairings
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (A := A) (B := B) (κsource := κ) (κtarget := κ)
    hvsrc hsourceDeriv htargetDeriv u u' hSourcePairing hTargetPairing
    (by
      intro a a'
      exact congrArg (fun q : ℝ => κ * q)
        (CartanMap.TangentAlignment.map_app (g := g) (x₀ := x₀) (p₀ := p₀)
          L a a'))

end PairingRoute
end Poincare

