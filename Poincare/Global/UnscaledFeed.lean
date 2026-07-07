import Poincare.Global.TargetPackage

/-!
# Unscaled endpoint feeds from rescaled pinned formulas

This module isolates the bilinear algebra needed to convert the hosted
rescaled endpoint feeds

`B (T⁻¹ • w) (T⁻¹ • w')`

into the unscaled anchor feeds consumed by `EqualityChain`.  The only remaining
scalar input is stated explicitly as the normalization identity equating the
rescaled sine factor with the chain's unscaled factor.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UnscaledFeed

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- Bilinear scaling for any chart-metric pairing packaged as a continuous bilinear map. -/
theorem continuousLinearPairing_smul_smul
    (B : E →L[ℝ] E →L[ℝ] ℝ) (c d : ℝ) (u v : E) :
    B (c • u) (d • v) = c * d * B u v := by
  have hleft : B (c • u) = c • B u := by
    exact map_smul B c u
  have hright : (B u) (d • v) = d * B u v := by
    simp [map_smul (B u) d v]
  calc
    B (c • u) (d • v) = (c • B u) (d • v) := by rw [hleft]
    _ = c * (B u (d • v)) := by rfl
    _ = c * (d * B u v) := by rw [hright]
    _ = c * d * B u v := by ring

/-- The source anchor chart metric is bilinear under identical inverse rescalings. -/
theorem sourceAnchorChartMetric_inv_smul_inv_smul
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T : ℝ) (u v : E) :
    CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • u) (T⁻¹ • v) =
      (T⁻¹ * T⁻¹) * CartanMap.sourceAnchorChartMetric g x₀ u v := by
  simpa using
    continuousLinearPairing_smul_smul
      (CartanMap.sourceAnchorChartMetric g x₀) T⁻¹ T⁻¹ u v

/-- The target anchor chart metric is bilinear under identical inverse rescalings. -/
theorem targetAnchorChartMetric_inv_smul_inv_smul
    (p₀ : RoundSphere3) (T : ℝ) (u v : E) :
    CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • u) (T⁻¹ • v) =
      (T⁻¹ * T⁻¹) * CartanMap.targetAnchorChartMetric p₀ u v := by
  simpa using
    continuousLinearPairing_smul_smul
      (CartanMap.targetAnchorChartMetric p₀) T⁻¹ T⁻¹ u v

/--
Convert a source rescaled pinned endpoint formula to the unscaled source feed
expected by `EqualityChain`.

The scalar hypothesis is the exact remaining normalization:
`sin(T)^2 * T⁻² = sin(θ)^2`.
-/
theorem source_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    {base : E} {Ψ : E → ℝ → E × E} {T θ : ℝ}
    (hScale : Real.sin T ^ 2 * (T⁻¹ * T⁻¹) = Real.sin θ ^ 2)
    (hSourceRescaled :
      ∀ w w' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) base)
            (Ψ w T).1 (Ψ w' T).1 =
          Real.sin T ^ 2 *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w')) :
    ∀ w w' : E,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) base)
          (Ψ w T).1 (Ψ w' T).1 =
        Real.sin θ ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ w w' := by
  intro w w'
  calc
    CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) base)
        (Ψ w T).1 (Ψ w' T).1 =
      Real.sin T ^ 2 *
        CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') :=
        hSourceRescaled w w'
    _ = Real.sin T ^ 2 *
        ((T⁻¹ * T⁻¹) * CartanMap.sourceAnchorChartMetric g x₀ w w') := by
        rw [sourceAnchorChartMetric_inv_smul_inv_smul]
    _ =
      (Real.sin T ^ 2 * (T⁻¹ * T⁻¹)) *
        CartanMap.sourceAnchorChartMetric g x₀ w w' := by ring
    _ = Real.sin θ ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ w w' := by
        rw [hScale]

/--
Convert a target rescaled pinned endpoint formula to the unscaled target feed
expected by `EqualityChain`.

The scalar hypothesis is the exact remaining normalization:
`sin(T)^2 * T⁻² = sin(θ)^2`.
-/
theorem target_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
    (p₀ : RoundSphere3) {base : E} {Ψ : E → ℝ → E × E} {T θ : ℝ}
    (hScale : Real.sin T ^ 2 * (T⁻¹ * T⁻¹) = Real.sin θ ^ 2)
    (hTargetRescaled :
      ∀ w w' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) base)
            (Ψ w T).1 (Ψ w' T).1 =
          Real.sin T ^ 2 *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')) :
    ∀ w w' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) base)
          (Ψ w T).1 (Ψ w' T).1 =
        Real.sin θ ^ 2 * CartanMap.targetAnchorChartMetric p₀ w w' := by
  intro w w'
  calc
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) base)
        (Ψ w T).1 (Ψ w' T).1 =
      Real.sin T ^ 2 *
        CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') :=
        hTargetRescaled w w'
    _ = Real.sin T ^ 2 *
        ((T⁻¹ * T⁻¹) * CartanMap.targetAnchorChartMetric p₀ w w') := by
        rw [targetAnchorChartMetric_inv_smul_inv_smul]
    _ =
      (Real.sin T ^ 2 * (T⁻¹ * T⁻¹)) *
        CartanMap.targetAnchorChartMetric p₀ w w' := by ring
    _ = Real.sin θ ^ 2 * CartanMap.targetAnchorChartMetric p₀ w w' := by
        rw [hScale]

/--
Feed rescaled source and target pinned formulas through the existing
`EqualityChain` endpoint-pairing bridge after bilinear unscaling.
-/
theorem hosted_endpoint_pairing_feed_of_rescaled_sin_sq_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {Ψs Ψt : E → ℝ → E × E} {Ts Tt θs θt : ℝ}
    (hSourceScale :
      Real.sin Ts ^ 2 * (Ts⁻¹ * Ts⁻¹) = Real.sin θs ^ 2)
    (hTargetScale :
      Real.sin Tt ^ 2 * (Tt⁻¹ * Tt⁻¹) = Real.sin θt ^ 2)
    (hSin : Real.sin θt ^ 2 = Real.sin θs ^ 2)
    (hSourceRescaled :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a Ts).1 (Ψs a' Ts).1 =
          Real.sin Ts ^ 2 *
            CartanMap.sourceAnchorChartMetric g x₀ (Ts⁻¹ • a) (Ts⁻¹ • a'))
    (hTargetRescaled :
      ∀ w w' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w Tt).1 (Ψt w' Tt).1 =
          Real.sin Tt ^ 2 *
            CartanMap.targetAnchorChartMetric p₀ (Tt⁻¹ • w) (Tt⁻¹ • w')) :
    ∀ a a' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a Ts).1 (Ψs a' Ts).1 := by
  refine
    EqualityChain.hosted_endpoint_pairing_feed_of_sin_sq_anchor_pairings
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (Ψs := Ψs) (Ψt := Ψt)
      (Ts := Ts) (Tt := Tt) (θs := θs) (θt := θt)
      hSin
      ?_
      ?_
  · exact
      source_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
        (g := g) (x₀ := x₀) (base := v) (Ψ := Ψs)
        (T := Ts) (θ := θs) hSourceScale hSourceRescaled
  · intro a a'
    exact
      target_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
        (p₀ := p₀) (base := L v) (Ψ := Ψt)
        (T := Tt) (θ := θt) hTargetScale hTargetRescaled
        (L a) (L a')

/--
Local-isometry consumer with both hosted endpoint feeds supplied in the
rescaled pinned form exported by the cascade packages.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_rescaled_sin_sq_hosted_anchor_pairings
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
    (hSourceScale :
      Real.sin Ts ^ 2 * (Ts⁻¹ * Ts⁻¹) = Real.sin θs ^ 2)
    (hTargetScale :
      Real.sin Tt ^ 2 * (Tt⁻¹ * Tt⁻¹) = Real.sin θt ^ 2)
    (hSin : Real.sin θt ^ 2 = Real.sin θs ^ 2)
    (hSourceRescaled :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a Ts).1 (Ψs a' Ts).1 =
          Real.sin Ts ^ 2 *
            CartanMap.sourceAnchorChartMetric g x₀ (Ts⁻¹ • a) (Ts⁻¹ • a'))
    (hTargetRescaled :
      ∀ w w' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w Tt).1 (Ψt w' Tt).1 =
          Real.sin Tt ^ 2 *
            CartanMap.targetAnchorChartMetric p₀ (Tt⁻¹ • w) (Tt⁻¹ • w')) :
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
  EqualityChain.cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pairings
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (A := A) (B := B) (Ψs := Ψs) (Ψt := Ψt)
    (Ts := Ts) (Tt := Tt) (θs := θs) (θt := θt)
    hA hB hvsrc hsourceDeriv htargetDeriv u u' hSin
    (source_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
      (g := g) (x₀ := x₀) (base := v) (Ψ := Ψs)
      (T := Ts) (θ := θs) hSourceScale hSourceRescaled)
    (by
      intro a a'
      exact
        target_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
          (p₀ := p₀) (base := L v) (Ψ := Ψt)
          (T := Tt) (θ := θt) hTargetScale hTargetRescaled
          (L a) (L a'))

end UnscaledFeed
end Poincare
