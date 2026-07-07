import Poincare.Global.PairingFeed

/-!
# Pairing-based endpoint equivalence upgrade

This module isolates the non-action route from a hosted endpoint CLM to a
continuous linear equivalence.  If the pullback of any endpoint pairing by a
linear map is a positive-definite source pairing, the linear map has trivial
kernel; finite dimensionality upgrades it to a continuous linear equivalence.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace PairingUpgrade

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
A continuous linear endomorphism whose pullback pairing is positive definite
has trivial kernel.
-/
theorem injective_of_pullback_posDef
    {D : E →L[ℝ] E} {G S : E →L[ℝ] E →L[ℝ] ℝ}
    (hSpos : ∀ {u : E}, u ≠ 0 → 0 < S u u)
    (hPullback : ∀ u u' : E, G (D u) (D u') = S u u') :
    Function.Injective D := by
  have hker : ∀ u : E, D u = 0 → u = 0 := by
    intro u hDu
    by_contra hu
    have hpos : 0 < S u u := hSpos hu
    have hzero : S u u = 0 := by
      have hpull := hPullback u u
      simpa [hDu] using hpull.symm
    exact (ne_of_gt hpos) hzero
  intro u u' huu'
  apply sub_eq_zero.mp
  apply hker (u - u')
  simp [map_sub, huu']

/--
Positive-definite pullback pairing upgrades an endpoint CLM to a continuous
linear equivalence with the same underlying continuous linear map.
-/
theorem exists_continuousLinearEquiv_of_pullback_posDef
    {D : E →L[ℝ] E} {G S : E →L[ℝ] E →L[ℝ] ℝ}
    (hSpos : ∀ {u : E}, u ≠ 0 → 0 < S u u)
    (hPullback : ∀ u u' : E, G (D u) (D u') = S u u') :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D := by
  have hDinj : Function.Injective D :=
    injective_of_pullback_posDef (D := D) (G := G) (S := S) hSpos hPullback
  let Aₗ : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo D.toLinearMap hDinj
  refine ⟨Aₗ.toContinuousLinearEquiv, ?_⟩
  ext u
  simp [Aₗ]

/-- Source-anchor specialization of the positive-definite pullback upgrade. -/
theorem exists_continuousLinearEquiv_of_sourceAnchor_pullback
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {D : E →L[ℝ] E} {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hPullback : ∀ u u' : E,
      G (D u) (D u') = CartanMap.sourceAnchorChartMetric g x₀ u u') :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D :=
  exists_continuousLinearEquiv_of_pullback_posDef
    (D := D) (G := G) (S := CartanMap.sourceAnchorChartMetric g x₀)
    (fun hu => CartanMap.sourceAnchorChartMetric_pos g x₀ hu)
    hPullback

/-- Target-anchor specialization of the positive-definite pullback upgrade. -/
theorem exists_continuousLinearEquiv_of_targetAnchor_pullback
    (p₀ : RoundSphere3)
    {D : E →L[ℝ] E} {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hPullback : ∀ u u' : E,
      G (D u) (D u') = CartanMap.targetAnchorChartMetric p₀ u u') :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D :=
  exists_continuousLinearEquiv_of_pullback_posDef
    (D := D) (G := G) (S := CartanMap.targetAnchorChartMetric p₀)
    (fun hu => CartanMap.targetAnchorChartMetric_pos p₀ hu)
    hPullback

/--
Hosted source endpoint CLM upgrade.  The hypothesis is stated on the hosted
endpoint positions; `linearizedEndpointCLM_pairing_eq_state_endpoint_pairing`
turns it into the required CLM pullback identity.
-/
theorem exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_pullback
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Ψ : E → ℝ → E × E} {T : ℝ}
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hEndpointPullback : ∀ u u' : E,
      G (Ψ u T).1 (Ψ u' T).1 =
        CartanMap.sourceAnchorChartMetric g x₀ u u') :
    ∃ A : E ≃L[ℝ] E,
      (A : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul := by
  refine
    exists_continuousLinearEquiv_of_sourceAnchor_pullback
      (g := g) (x₀ := x₀)
      (D := linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) (G := G) ?_
  intro u u'
  calc
    G (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u)
        (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u') =
      G (Ψ u T).1 (Ψ u' T).1 :=
        PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
          (G := G) (Ψ := Ψ) (T := T) hadd hsmul u u'
    _ = CartanMap.sourceAnchorChartMetric g x₀ u u' :=
        hEndpointPullback u u'

/-- Target analogue of `exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_pullback`. -/
theorem exists_continuousLinearEquiv_of_target_linearizedEndpointCLM_pullback
    (p₀ : RoundSphere3)
    {Ψ : E → ℝ → E × E} {T : ℝ}
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hEndpointPullback : ∀ u u' : E,
      G (Ψ u T).1 (Ψ u' T).1 =
        CartanMap.targetAnchorChartMetric p₀ u u') :
    ∃ A : E ≃L[ℝ] E,
      (A : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul := by
  refine
    exists_continuousLinearEquiv_of_targetAnchor_pullback
      (p₀ := p₀)
      (D := linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) (G := G) ?_
  intro u u'
  calc
    G (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u)
        (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u') =
      G (Ψ u T).1 (Ψ u' T).1 :=
        PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
          (G := G) (Ψ := Ψ) (T := T) hadd hsmul u u'
    _ = CartanMap.targetAnchorChartMetric p₀ u u' :=
        hEndpointPullback u u'

/--
Pairing-feed adapter with `A` and `B` constructed from positive-definite
source and target pullback identities.
-/
theorem exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_hosted_anchor_pullbacks
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {Ψs Ψt : E → ℝ → E × E} {T : ℝ}
    {hadds : ∀ w w' : E,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E),
      (Ψs (c • w) T).1 = c • (Ψs w T).1}
    {haddt : ∀ w w' : E,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E),
      (Ψt (c • w) T).1 = c • (Ψt w T).1}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult) (L v))
    (u u' : E)
    (hSourcePullback :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPullback :
      ∀ b b' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt b T).1 (Ψt b' T).1 =
          CartanMap.targetAnchorChartMetric p₀ b b') :
    ∃ A B : E ≃L[ℝ] E,
      (A : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls ∧
      (B : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult ∧
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
  let Gs : E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
  let Gt : E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v))
  rcases
      exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_pullback
        (g := g) (x₀ := x₀) (Ψ := Ψs) (T := T) hadds hsmuls
        (G := Gs) (by intro a a'; exact hSourcePullback a a') with
    ⟨A, hA⟩
  rcases
      exists_continuousLinearEquiv_of_target_linearizedEndpointCLM_pullback
        (p₀ := p₀) (Ψ := Ψt) (T := T) haddt hsmult
        (G := Gt) (by intro b b'; exact hTargetPullback b b') with
    ⟨B, hB⟩
  refine ⟨A, B, hA, hB, ?_⟩
  refine
    PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (A := A) (B := B) (Ψs := Ψs) (Ψt := Ψt)
      (Ts := T) (Tt := T) hA hB hvsrc ?_ ?_ u u' ?_
  · simpa [hA] using hsourceDeriv
  · simpa [hB] using htargetDeriv
  · intro a a'
    calc
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) T).1 (Ψt (L a') T).1 =
        CartanMap.targetAnchorChartMetric p₀ (L a) (L a') :=
          hTargetPullback (L a) (L a')
      _ = CartanMap.sourceAnchorChartMetric g x₀ a a' :=
          CartanMap.TangentAlignment.map_app L a a'
      _ =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 :=
          (hSourcePullback a a').symm

end PairingUpgrade
end Poincare
