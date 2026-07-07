import Poincare.Global.PairingRoute

/-!
# Endpoint-pairing feed boundary

This module feeds the hosted endpoint pairings into the derivative-pairing
Cartan bridge.  The remaining geometric obligation is isolated as one
endpoint-pairing equality between the hosted source and target linearized
families.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace PairingFeed

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Direct Cartan pullback from a single derivative endpoint-pairing equality.

This is the smallest consumer after the two hosted sides have been aligned:
the source and target derivative endpoint pairings agree on corresponding
initial directions.  The strict derivative part is still supplied by the
existing Cartan chain rule.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_derivative_endpoint_pairing_equality
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
    (hEndpointPairing :
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) =
          CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a')) :
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
    have htarget :
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (CartanLocalIsometry.cartanChartDifferential L A B u)
            (CartanLocalIsometry.cartanChartDifferential L A B u') =
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) := by
      simp [CartanLocalIsometry.cartanChartDifferential, a, a']
    have hsource :
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a') =
          CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            u u' := by
      simp [a, a']
    calc
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (CartanLocalIsometry.cartanChartDifferential L A B u)
          (CartanLocalIsometry.cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) := htarget
      _ =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a') := hEndpointPairing a a'
      _ =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' := hsource

/--
Hosted endpoint version of the preceding theorem.

If the source and target strict derivative equivalences are the endpoint CLMs
of hosted linearized families, the only remaining feed is the equality of the
two hosted `Ψ.1` endpoint pairings.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    {Ψs Ψt : E → ℝ → E × E} {Ts Tt : ℝ}
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
    (hEndpointPairingFeed :
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
          CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a Ts).1 (Ψs a' Ts).1) :
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
  refine
    cartanMap_isLocalIsometry_on_normalBall_of_derivative_endpoint_pairing_equality
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (A := A) (B := B)
      hvsrc hsourceDeriv htargetDeriv u u' ?_
  intro a a'
  let Gs : E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
  let Gt : E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v))
  have htCLM :
      Gt (linearizedEndpointCLM (Ψ := Ψt) Tt haddt hsmult (L a))
          (linearizedEndpointCLM (Ψ := Ψt) Tt haddt hsmult (L a')) =
        Gt (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 :=
    PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
      (G := Gt) (Ψ := Ψt) (T := Tt) haddt hsmult (L a) (L a')
  have hsCLM :
      Gs (linearizedEndpointCLM (Ψ := Ψs) Ts hadds hsmuls a)
          (linearizedEndpointCLM (Ψ := Ψs) Ts hadds hsmuls a') =
        Gs (Ψs a Ts).1 (Ψs a' Ts).1 :=
    PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
      (G := Gs) (Ψ := Ψs) (T := Ts) hadds hsmuls a a'
  calc
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        ((B : E →L[ℝ] E) (L a)) ((B : E →L[ℝ] E) (L a')) =
      Gt (linearizedEndpointCLM (Ψ := Ψt) Tt haddt hsmult (L a))
        (linearizedEndpointCLM (Ψ := Ψt) Tt haddt hsmult (L a')) := by
        simp [Gt, hB]
    _ = Gt (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 := htCLM
    _ = Gs (Ψs a Ts).1 (Ψs a' Ts).1 := by
        simpa [Gs, Gt] using hEndpointPairingFeed a a'
    _ =
      Gs (linearizedEndpointCLM (Ψ := Ψs) Ts hadds hsmuls a)
        (linearizedEndpointCLM (Ψ := Ψs) Ts hadds hsmuls a') := hsCLM.symm
    _ =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        ((A : E →L[ℝ] E) a) ((A : E →L[ℝ] E) a') := by
        simp [Gs, hA]

end PairingFeed
end Poincare

