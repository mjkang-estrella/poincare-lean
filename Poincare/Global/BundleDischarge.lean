import Poincare.Global.OneSidedPayload
import Poincare.Global.CombinedFeed

/-!
# Bundle discharge boundary

This module discharges the part of the M5 bundle made available by the
one-sided transverse Gauss payload: transverse endpoint orthogonality can now
be obtained on `Icc 0 T` for the rescaled hosted data and fed into the
corrected `T ^ 2` radial consumer.

The theorem at the bottom is not curvature-only.  It still consumes the
common-time ray, speed, and transverse/transverse endpoint blocks that the
current exported cascade does not yet package as one radius intersection.
-/

noncomputable section

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace BundleDischarge

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

omit [T2Space M] in
/-- Rescaling both slots preserves source-anchor transverse orthogonality. -/
theorem sourceAnchorChartMetric_inv_smul_transversePart_eq_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {T : ℝ} (v a : E3) :
    CartanMap.sourceAnchorChartMetric g x0
        (T⁻¹ • v)
        (T⁻¹ • CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  have horth :
      CartanMap.sourceAnchorChartMetric g x0 v
          (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a) = 0 :=
    CartanPullback.transversePart_pair_self_left
      (B := CartanMap.sourceAnchorChartMetric g x0) (v := v) (u := a)
      (CartanMap.sourceAnchorChartMetric_symm g x0)
      (CartanPullback.sourceAnchorChartMetric_self_ne_zero (g := g) (x₀ := x0) hv)
  simp [horth]

omit [T2Space M] in
/-- Rescaling both slots preserves target-anchor transverse orthogonality. -/
theorem targetAnchorChartMetric_inv_smul_transversePart_eq_zero
    (p0 : RoundSphere3) {T : ℝ} (v a : E3) :
    CartanMap.targetAnchorChartMetric p0
        (T⁻¹ • v)
        (T⁻¹ • CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) v a) = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  have horth :
      CartanMap.targetAnchorChartMetric p0 v
          (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v a) = 0 :=
    CartanPullback.transversePart_pair_self_left
      (B := CartanMap.targetAnchorChartMetric p0) (v := v) (u := a)
      (CartanMap.targetAnchorChartMetric_symm p0)
      (CartanPullback.targetAnchorChartMetric_self_ne_zero (p₀ := p0) hv)
  simp [horth]

omit [T2Space M] in
/--
Source one-sided payload specialized to hosted endpoint coordinates.

The base velocity is `T⁻¹ • v`, while the transverse linearized input is the
rescaled transverse endpoint component.
-/
theorem source_transverse_endpoint_orthogonal_of_oneSided_payload
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {alpha : E3 × E3 → ℝ → E3 × E3} {Psi : E3 → ℝ → E3 × E3}
    {v : E3} {T : ℝ} (hT : 0 < T) (a : E3)
    (hbase : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (alpha (extChartAt I3 x0 x0, T⁻¹ • v))
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x0)
          (alpha (extChartAt I3 x0 x0, T⁻¹ • v) tau))
        (Icc (0 : ℝ) T) tau)
    (hPsi : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (Psi (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x0)
          (alpha (extChartAt I3 x0 x0, T⁻¹ • v)) tau
          (Psi (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a) tau))
        (Icc (0 : ℝ) T) tau)
    (hflow : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ =>
          alpha
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau)
        (Psi (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) tau) 0)
    (hspeed_const : ∀ tau ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric g x0
          (alpha
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau).1
          (alpha
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau).2
          (alpha
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric g x0 (extChartAt I3 x0 x0)
          (T⁻¹ • v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a))
          (T⁻¹ • v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a))))
    (hGd_base : ∀ tau ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (GeodesicTransport.chartGeodesicMetric g x0)
        (alpha (extChartAt I3 x0 x0, T⁻¹ • v) tau).1)
    (hGd_initial :
      DifferentiableAt ℝ (GeodesicTransport.chartGeodesicMetric g x0)
        (extChartAt I3 x0 x0))
    (halpha0 :
      alpha (extChartAt I3 x0 x0, T⁻¹ • v) 0 =
        (extChartAt I3 x0 x0, T⁻¹ • v))
    (hPsi0 :
      Psi (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) 0 =
        ((0 : E3),
          T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a))
    (hcut : ∀ tau ∈ Icc (0 : ℝ) T,
      GeodesicTransport.cutoff (n := 3) x0
        (alpha (extChartAt I3 x0 x0, T⁻¹ • v) tau).1 = 1) :
    ∀ tau ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x0
        (alpha (extChartAt I3 x0 x0, T⁻¹ • v) tau).1
        (Psi (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) tau).1
        (alpha (extChartAt I3 x0 x0, T⁻¹ • v) tau).2 = 0 := by
  exact
    OrthogonalityFeed.source_transverse_horth_on_Icc_of_oneSided_payload
      (g := g) (x₀ := x0) (α := alpha)
      (v := T⁻¹ • v)
      (w := T⁻¹ • CartanPullback.transversePart
        (CartanMap.sourceAnchorChartMetric g x0) v a)
      (Ψ := Psi (CartanPullback.transversePart
        (CartanMap.sourceAnchorChartMetric g x0) v a))
      (T := T) hT hbase hPsi hflow hspeed_const hGd_base hGd_initial
      halpha0 hPsi0
      (sourceAnchorChartMetric_inv_smul_transversePart_eq_zero
        (g := g) (x0 := x0) (T := T) v a)
      hcut

/-- Target one-sided payload specialized to hosted endpoint coordinates. -/
theorem target_transverse_endpoint_orthogonal_of_oneSided_payload
    (p0 : RoundSphere3)
    {alpha : E3 × E3 → ℝ → E3 × E3} {Psi : E3 → ℝ → E3 × E3}
    {v : E3} {T : ℝ} (hT : 0 < T) (a : E3)
    (hbase : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (alpha (extChartAt I3 p0 p0, T⁻¹ • v))
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p0)
          (alpha (extChartAt I3 p0 p0, T⁻¹ • v) tau))
        (Icc (0 : ℝ) T) tau)
    (hPsi : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (Psi (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) v a))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p0)
          (alpha (extChartAt I3 p0 p0, T⁻¹ • v)) tau
          (Psi (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v a) tau))
        (Icc (0 : ℝ) T) tau)
    (hflow : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ =>
          alpha
            (extChartAt I3 p0 p0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) v a))
            tau)
        (Psi (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) v a) tau) 0)
    (hspeed_const : ∀ tau ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0
          (alpha
            (extChartAt I3 p0 p0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) v a))
            tau).1
          (alpha
            (extChartAt I3 p0 p0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) v a))
            tau).2
          (alpha
            (extChartAt I3 p0 p0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) v a))
            tau).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0
          (extChartAt I3 p0 p0)
          (T⁻¹ • v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) v a))
          (T⁻¹ • v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) v a))))
    (hGd_base : ∀ tau ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ
        (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0)
        (alpha (extChartAt I3 p0 p0, T⁻¹ • v) tau).1)
    (hGd_initial :
      DifferentiableAt ℝ
        (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0)
        (extChartAt I3 p0 p0))
    (halpha0 :
      alpha (extChartAt I3 p0 p0, T⁻¹ • v) 0 =
        (extChartAt I3 p0 p0, T⁻¹ • v))
    (hPsi0 :
      Psi (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) v a) 0 =
        ((0 : E3),
          T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) v a))
    (hcut : ∀ tau ∈ Icc (0 : ℝ) T,
      GeodesicTransport.cutoff (n := 3) p0
        (alpha (extChartAt I3 p0 p0, T⁻¹ • v) tau).1 = 1) :
    ∀ tau ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        (alpha (extChartAt I3 p0 p0, T⁻¹ • v) tau).1
        (Psi (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) v a) tau).1
        (alpha (extChartAt I3 p0 p0, T⁻¹ • v) tau).2 = 0 := by
  exact
    OrthogonalityFeed.target_transverse_horth_on_Icc_of_oneSided_payload
      (p₀ := p0) (α := alpha)
      (v := T⁻¹ • v)
      (w := T⁻¹ • CartanPullback.transversePart
        (CartanMap.targetAnchorChartMetric p0) v a)
      (Ψ := Psi (CartanPullback.transversePart
        (CartanMap.targetAnchorChartMetric p0) v a))
      (T := T) hT hbase hPsi hflow hspeed_const hGd_base hGd_initial
      halpha0 hPsi0
      (targetAnchorChartMetric_inv_smul_transversePart_eq_zero
        (p0 := p0) (T := T) v a)
      hcut

omit [T2Space M] in
/--
One common endpoint feed into the corrected `T ^ 2` radial consumer, with
transverse orthogonality discharged from the one-sided payload fields.
-/
theorem cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed
    {g : ClosedSmoothRiemannianMetric 3 M} {x0 : M} {p0 : RoundSphere3}
    (L : CartanMap.TangentAlignment g x0 p0)
    {v Vs Vt : E3} {A B : E3 ≃L[ℝ] E3}
    {PsiS PsiT : E3 → ℝ → E3 × E3}
    {alphaS alphaT : E3 × E3 → ℝ → E3 × E3}
    {speed T : ℝ} (hTpos : 0 < T)
    {hadds : ∀ w w' : E3,
      (PsiS (w + w') T).1 = (PsiS w T).1 + (PsiS w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E3),
      (PsiS (c • w) T).1 = c • (PsiS w T).1}
    {haddt : ∀ w w' : E3,
      (PsiT (w + w') T).1 = (PsiT w T).1 + (PsiT w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E3),
      (PsiT (c • w) T).1 = c • (PsiT w T).1}
    (hA :
      (A : E3 →L[ℝ] E3) =
        linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls)
    (hB :
      (B : E3 →L[ℝ] E3) =
        linearizedEndpointCLM (Ψ := PsiT) T haddt hsmult)
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0)
        (A : E3 →L[ℝ] E3) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0)
        (B : E3 →L[ℝ] E3) (L v))
    (u u' : E3)
    (hSourceEndpoint :
      (alphaS (extChartAt I3 x0 x0, T⁻¹ • v) T).1 =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
    (hSourceVelocity :
      (alphaS (extChartAt I3 x0 x0, T⁻¹ • v) T).2 = Vs)
    (hTargetEndpoint :
      (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) T).1 =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) (L v))
    (hTargetVelocity :
      (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) T).2 = Vt)
    (hSourceRay : (PsiS v T).1 = T • Vs)
    (hTargetRay : (PsiT (L v) T).1 = T • Vt)
    (hSourceEndpointSpeed :
      CovariantDerivative.chartMetric g.inner x0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
          Vs Vs = speed ^ 2)
    (hTargetEndpointSpeed :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0) (L v))
          Vt Vt = speed ^ 2)
    (hSourceAnchorSpeed :
      CartanMap.sourceAnchorChartMetric g x0 (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (hTargetAnchorSpeed :
      CartanMap.targetAnchorChartMetric p0 (T⁻¹ • L v) (T⁻¹ • L v) = speed ^ 2)
    (hSourceBase : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (alphaS (extChartAt I3 x0 x0, T⁻¹ • v))
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x0)
          (alphaS (extChartAt I3 x0 x0, T⁻¹ • v) tau))
        (Icc (0 : ℝ) T) tau)
    (hSourcePsi : ∀ a : E3, ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (PsiS (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x0)
          (alphaS (extChartAt I3 x0 x0, T⁻¹ • v)) tau
          (PsiS (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a) tau))
        (Icc (0 : ℝ) T) tau)
    (hSourceFlow : ∀ a : E3, ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ =>
          alphaS
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau)
        (PsiS (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) tau) 0)
    (hSourceSpeedConst : ∀ a : E3, ∀ tau ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric g x0
          (alphaS
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau).1
          (alphaS
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau).2
          (alphaS
            (extChartAt I3 x0 x0,
              T⁻¹ • v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x0) v a))
            tau).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric g x0 (extChartAt I3 x0 x0)
          (T⁻¹ • v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a))
          (T⁻¹ • v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a))))
    (hSourceGdBase : ∀ tau ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (GeodesicTransport.chartGeodesicMetric g x0)
        (alphaS (extChartAt I3 x0 x0, T⁻¹ • v) tau).1)
    (hSourceGdInitial :
      DifferentiableAt ℝ (GeodesicTransport.chartGeodesicMetric g x0)
        (extChartAt I3 x0 x0))
    (hSourceAlpha0 :
      alphaS (extChartAt I3 x0 x0, T⁻¹ • v) 0 =
        (extChartAt I3 x0 x0, T⁻¹ • v))
    (hSourcePsi0 : ∀ a : E3,
      PsiS (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) 0 =
        ((0 : E3),
          T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a))
    (hSourceCut : ∀ tau ∈ Icc (0 : ℝ) T,
      GeodesicTransport.cutoff (n := 3) x0
        (alphaS (extChartAt I3 x0 x0, T⁻¹ • v) tau).1 = 1)
    (hTargetBase : ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v))
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p0)
          (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) tau))
        (Icc (0 : ℝ) T) tau)
    (hTargetPsi : ∀ a : E3, ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (PsiT (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) (L v) a))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p0)
          (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v)) tau
          (PsiT (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) (L v) a) tau))
        (Icc (0 : ℝ) T) tau)
    (hTargetFlow : ∀ a : E3, ∀ tau ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ =>
          alphaT
            (extChartAt I3 p0 p0,
              T⁻¹ • L v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a))
            tau)
        (PsiT (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) (L v) a) tau) 0)
    (hTargetSpeedConst : ∀ a : E3, ∀ tau ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0
          (alphaT
            (extChartAt I3 p0 p0,
              T⁻¹ • L v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a))
            tau).1
          (alphaT
            (extChartAt I3 p0 p0,
              T⁻¹ • L v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a))
            tau).2
          (alphaT
            (extChartAt I3 p0 p0,
              T⁻¹ • L v +
                r • (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p0) (L v) a))
            tau).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0
          (extChartAt I3 p0 p0)
          (T⁻¹ • L v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a))
          (T⁻¹ • L v +
            r • (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a))))
    (hTargetGdBase : ∀ tau ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ
        (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0)
        (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) tau).1)
    (hTargetGdInitial :
      DifferentiableAt ℝ
        (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p0)
        (extChartAt I3 p0 p0))
    (hTargetAlpha0 :
      alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) 0 =
        (extChartAt I3 p0 p0, T⁻¹ • L v))
    (hTargetPsi0 : ∀ a : E3,
      PsiT (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) (L v) a) 0 =
        ((0 : E3),
          T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) (L v) a))
    (hTargetCut : ∀ tau ∈ Icc (0 : ℝ) T,
      GeodesicTransport.cutoff (n := 3) p0
        (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) tau).1 = 1)
    (hSourceTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v a'))
    (hTargetTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) a')) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x0 p0 L)
        (CartanLocalIsometry.cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0) (L v))
          (CartanLocalIsometry.cartanChartDifferential L A B u)
          (CartanLocalIsometry.cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
          u u' := by
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨le_of_lt hTpos, le_rfl⟩
  refine
    CombinedFeed.cartanMap_isLocalIsometry_of_common_ray_speed_orthogonal_transverse_feed
      (g := g) (x0 := x0) (p0 := p0) L
      (v := v) (Vs := Vs) (Vt := Vt) (A := A) (B := B)
      (PsiS := PsiS) (PsiT := PsiT) (speed := speed) (T := T)
      hA hB hvsrc hsourceDeriv htargetDeriv u u'
      hSourceRay hTargetRay hSourceEndpointSpeed hTargetEndpointSpeed
      hSourceAnchorSpeed hTargetAnchorSpeed ?_ ?_
      hSourceTransverseTransverse hTargetTransverseTransverse
  · intro a
    have horth :=
      source_transverse_endpoint_orthogonal_of_oneSided_payload
        (g := g) (x0 := x0) (alpha := alphaS) (Psi := PsiS)
        (v := v) (T := T) hTpos a
        hSourceBase (hSourcePsi a) (hSourceFlow a) (hSourceSpeedConst a)
        hSourceGdBase hSourceGdInitial hSourceAlpha0 (hSourcePsi0 a)
        hSourceCut T hTmem
    have hSourceEndpoint' :
        (alphaS (extChartAt I3 x0 x0, T⁻¹ • v) T).1 =
          extChartAt I3 x0 (GeodesicTransport.expAt g x0 v) := by
      simpa [GeodesicTransport.expAtChartOpenPartialHomeomorph_coe]
        using hSourceEndpoint
    rw [hSourceEndpoint', hSourceVelocity] at horth
    simpa using horth
  · intro a
    have horth :=
      target_transverse_endpoint_orthogonal_of_oneSided_payload
        (p0 := p0) (alpha := alphaT) (Psi := PsiT)
        (v := L v) (T := T) hTpos a
        hTargetBase (hTargetPsi a) (hTargetFlow a) (hTargetSpeedConst a)
        hTargetGdBase hTargetGdInitial hTargetAlpha0 (hTargetPsi0 a)
        hTargetCut T hTmem
    have hTargetEndpoint' :
        (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) T).1 =
          extChartAt I3 p0 (GeodesicTransport.expAt roundSphereMetric3 p0 (L v)) := by
      simpa [GeodesicTransport.expAtChartOpenPartialHomeomorph_coe]
        using hTargetEndpoint
    rw [hTargetEndpoint', hTargetVelocity] at horth
    simpa using horth

end BundleDischarge
end Poincare
