import Poincare.Global.PairingUpgrade

/-!
# Scaled positive-definite endpoint upgrade

This module is the scaled variant of `PairingUpgrade`: a hosted endpoint CLM
does not need an exact unscaled positive-definite pullback in order to upgrade
to a continuous linear equivalence.  A pullback by any strictly positive common
scalar is enough for injectivity, hence for the finite-dimensional endomorphism
upgrade used by the Cartan pairing consumer.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace ScaledUpgrade

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- A positive sine-square factor is available on a shrunk angle interval. -/
theorem sin_sq_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    0 < Real.sin θ ^ 2 :=
  sq_pos_of_pos (Real.sin_pos_of_mem_Ioo hθ)

/--
A continuous linear endomorphism whose pullback pairing is a positive scalar
multiple of a positive-definite source pairing has trivial kernel.
-/
theorem injective_of_scaled_pullback_posDef
    {D : E →L[ℝ] E} {G S : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ}
    (hc : 0 < c)
    (hSpos : ∀ {u : E}, u ≠ 0 → 0 < S u u)
    (hPullback : ∀ u u' : E, G (D u) (D u') = c * S u u') :
    Function.Injective D := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hker : ∀ u : E, D u = 0 → u = 0 := by
    intro u hDu
    by_contra hu
    have hpos : 0 < S u u := hSpos hu
    have hscaled_zero : c * S u u = 0 := by
      have hpull := hPullback u u
      simpa [hDu] using hpull.symm
    have hzero : S u u = 0 :=
      (mul_eq_zero.mp hscaled_zero).resolve_left hcne
    exact (ne_of_gt hpos) hzero
  intro u u' huu'
  apply sub_eq_zero.mp
  apply hker (u - u')
  simp [map_sub, huu']

/--
Positive scaled pullback pairing upgrades an endpoint CLM to a continuous
linear equivalence with the same underlying continuous linear map.
-/
theorem exists_continuousLinearEquiv_of_scaled_pullback_posDef
    {D : E →L[ℝ] E} {G S : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ}
    (hc : 0 < c)
    (hSpos : ∀ {u : E}, u ≠ 0 → 0 < S u u)
    (hPullback : ∀ u u' : E, G (D u) (D u') = c * S u u') :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D := by
  have hDinj : Function.Injective D :=
    injective_of_scaled_pullback_posDef
      (D := D) (G := G) (S := S) hc hSpos hPullback
  let Aₗ : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo D.toLinearMap hDinj
  refine ⟨Aₗ.toContinuousLinearEquiv, ?_⟩
  ext u
  simp [Aₗ]

/-- Source-anchor specialization of the scaled positive-definite upgrade. -/
theorem exists_continuousLinearEquiv_of_scaled_sourceAnchor_pullback
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {D : E →L[ℝ] E} {G : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ}
    (hc : 0 < c)
    (hPullback : ∀ u u' : E,
      G (D u) (D u') = c * CartanMap.sourceAnchorChartMetric g x₀ u u') :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D :=
  exists_continuousLinearEquiv_of_scaled_pullback_posDef
    (D := D) (G := G) (S := CartanMap.sourceAnchorChartMetric g x₀) hc
    (fun hu => CartanMap.sourceAnchorChartMetric_pos g x₀ hu)
    hPullback

/-- Target-anchor specialization of the scaled positive-definite upgrade. -/
theorem exists_continuousLinearEquiv_of_scaled_targetAnchor_pullback
    (p₀ : RoundSphere3)
    {D : E →L[ℝ] E} {G : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ}
    (hc : 0 < c)
    (hPullback : ∀ u u' : E,
      G (D u) (D u') = c * CartanMap.targetAnchorChartMetric p₀ u u') :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D :=
  exists_continuousLinearEquiv_of_scaled_pullback_posDef
    (D := D) (G := G) (S := CartanMap.targetAnchorChartMetric p₀) hc
    (fun hu => CartanMap.targetAnchorChartMetric_pos p₀ hu)
    hPullback

/--
Hosted source endpoint CLM upgrade from a positive scaled endpoint pullback.
-/
theorem exists_continuousLinearEquiv_of_scaled_source_linearizedEndpointCLM_pullback
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Ψ : E → ℝ → E × E} {T c : ℝ}
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (a : ℝ) (w : E),
      (Ψ (a • w) T).1 = a • (Ψ w T).1)
    {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hc : 0 < c)
    (hEndpointPullback : ∀ u u' : E,
      G (Ψ u T).1 (Ψ u' T).1 =
        c * CartanMap.sourceAnchorChartMetric g x₀ u u') :
    ∃ A : E ≃L[ℝ] E,
      (A : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul := by
  refine
    exists_continuousLinearEquiv_of_scaled_sourceAnchor_pullback
      (g := g) (x₀ := x₀)
      (D := linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) (G := G) hc ?_
  intro u u'
  calc
    G (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u)
        (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u') =
      G (Ψ u T).1 (Ψ u' T).1 :=
        PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
          (G := G) (Ψ := Ψ) (T := T) hadd hsmul u u'
    _ = c * CartanMap.sourceAnchorChartMetric g x₀ u u' :=
        hEndpointPullback u u'

/--
Hosted target endpoint CLM upgrade from a positive scaled endpoint pullback.
-/
theorem exists_continuousLinearEquiv_of_scaled_target_linearizedEndpointCLM_pullback
    (p₀ : RoundSphere3)
    {Ψ : E → ℝ → E × E} {T c : ℝ}
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (a : ℝ) (w : E),
      (Ψ (a • w) T).1 = a • (Ψ w T).1)
    {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hc : 0 < c)
    (hEndpointPullback : ∀ u u' : E,
      G (Ψ u T).1 (Ψ u' T).1 =
        c * CartanMap.targetAnchorChartMetric p₀ u u') :
    ∃ A : E ≃L[ℝ] E,
      (A : E →L[ℝ] E) = linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul := by
  refine
    exists_continuousLinearEquiv_of_scaled_targetAnchor_pullback
      (p₀ := p₀)
      (D := linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) (G := G) hc ?_
  intro u u'
  calc
    G (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u)
        (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u') =
      G (Ψ u T).1 (Ψ u' T).1 :=
        PairingRoute.linearizedEndpointCLM_pairing_eq_state_endpoint_pairing
          (G := G) (Ψ := Ψ) (T := T) hadd hsmul u u'
    _ = c * CartanMap.targetAnchorChartMetric p₀ u u' :=
        hEndpointPullback u u'

/--
Pairing-feed adapter with `A` and `B` constructed from a common positive
scaled source/target pullback.  The final consumer accepts the scaled form
because the common scalar cancels across the tangent alignment.
-/
theorem exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_scaled_hosted_anchor_pullbacks
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {Ψs Ψt : E → ℝ → E × E} {T c : ℝ}
    {hadds : ∀ w w' : E,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (a : ℝ) (w : E),
      (Ψs (a • w) T).1 = a • (Ψs w T).1}
    {haddt : ∀ w w' : E,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (a : ℝ) (w : E),
      (Ψt (a • w) T).1 = a • (Ψt w T).1}
    (hc : 0 < c)
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
          c * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPullback :
      ∀ b b' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt b T).1 (Ψt b' T).1 =
          c * CartanMap.targetAnchorChartMetric p₀ b b') :
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
      exists_continuousLinearEquiv_of_scaled_source_linearizedEndpointCLM_pullback
        (g := g) (x₀ := x₀) (Ψ := Ψs) (T := T) hadds hsmuls
        (G := Gs) hc (by intro a a'; exact hSourcePullback a a') with
    ⟨A, hA⟩
  rcases
      exists_continuousLinearEquiv_of_scaled_target_linearizedEndpointCLM_pullback
        (p₀ := p₀) (Ψ := Ψt) (T := T) haddt hsmult
        (G := Gt) hc (by intro b b'; exact hTargetPullback b b') with
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
        c * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') :=
          hTargetPullback (L a) (L a')
      _ = c * CartanMap.sourceAnchorChartMetric g x₀ a a' := by
          rw [CartanMap.TangentAlignment.map_app L a a']
      _ =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 :=
          (hSourcePullback a a').symm

/--
The sine-square specialization used after shrinking to an angle in `(0, π)`.
-/
theorem exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pullbacks
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {Ψs Ψt : E → ℝ → E × E} {T θ : ℝ}
    {hadds : ∀ w w' : E,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (a : ℝ) (w : E),
      (Ψs (a • w) T).1 = a • (Ψs w T).1}
    {haddt : ∀ w w' : E,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (a : ℝ) (w : E),
      (Ψt (a • w) T).1 = a • (Ψt w T).1}
    (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
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
          Real.sin θ ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTargetPullback :
      ∀ b b' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt b T).1 (Ψt b' T).1 =
          Real.sin θ ^ 2 * CartanMap.targetAnchorChartMetric p₀ b b') :
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
            u u' :=
  exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_scaled_hosted_anchor_pullbacks
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (Ψs := Ψs) (Ψt := Ψt) (T := T) (c := Real.sin θ ^ 2)
    (sin_sq_pos_of_mem_Ioo hθ) hvsrc hsourceDeriv htargetDeriv u u'
    hSourcePullback hTargetPullback

end ScaledUpgrade
end Poincare
