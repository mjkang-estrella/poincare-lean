import Poincare.Global.SpeedReconcile

/-!
# Combined Cartan feed boundary

This module records the verified common-quantification feed into the corrected
radial consumer.  The radial blocks are supplied by `SpeedReconcile`; the mixed
blocks are derived from the radial ray identification plus endpoint
orthogonality for transverse inputs.

The curvature-only theorem is still blocked by the upstream absence of one
exported common-time package producing all endpoint speed, transverse
orthogonality, and transverse-pairing facts simultaneously.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CombinedFeed

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

/--
Ray identification plus endpoint orthogonality supplies the radial/transverse
endpoint mixed block.
-/
theorem radialPart_endpoint_pairing_eq_zero_of_ray_and_transverse_orthogonal
    (G B : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    {Psi : E3 → ℝ → E3 × E3} {v V : E3} {T : ℝ}
    (hsymm : ∀ x y : E3, G x y = G y x)
    (hRay : (Psi v T).1 = T • V)
    (hsmul : ∀ (c : ℝ) (w : E3), (Psi (c • w) T).1 = c • (Psi w T).1)
    (horth :
      ∀ a : E3,
        G ((Psi (CartanPullback.transversePart B v a) T).1) V = 0)
    (a a' : E3) :
    G ((Psi (CartanPullback.radialPart B v a) T).1)
      ((Psi (CartanPullback.transversePart B v a') T).1) = 0 := by
  calc
    G ((Psi (CartanPullback.radialPart B v a) T).1)
        ((Psi (CartanPullback.transversePart B v a') T).1) =
      G (CartanPullback.radialCoeff B v a • (Psi v T).1)
        ((Psi (CartanPullback.transversePart B v a') T).1) := by
          rw [show CartanPullback.radialPart B v a =
            CartanPullback.radialCoeff B v a • v from rfl]
          rw [hsmul]
    _ =
      G (CartanPullback.radialCoeff B v a • (T • V))
        ((Psi (CartanPullback.transversePart B v a') T).1) := by
          rw [hRay]
    _ =
      (CartanPullback.radialCoeff B v a * T) *
        G V ((Psi (CartanPullback.transversePart B v a') T).1) := by
          simp [smul_smul, mul_assoc]
    _ = 0 := by
          rw [hsymm V ((Psi (CartanPullback.transversePart B v a') T).1),
            horth a']
          simp

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Source mixed block in the shape required by the corrected radial consumer,
derived from the source ray and the endpoint orthogonality feed.
-/
theorem source_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {Psi : E3 → ℝ → E3 × E3} {v Vs : E3} {T : ℝ}
    (hRay : (Psi v T).1 = T • Vs)
    (hsmul : ∀ (c : ℝ) (w : E3), (Psi (c • w) T).1 = c • (Psi w T).1)
    (horth :
      ∀ a : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((Psi (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1) Vs = 0)
    (a a' : E3) :
    CovariantDerivative.chartMetric g.inner x0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
        ((Psi (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
        ((Psi (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) = 0 := by
  exact
    radialPart_endpoint_pairing_eq_zero_of_ray_and_transverse_orthogonal
      (G := CovariantDerivative.chartMetric g.inner x0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v))
      (B := CartanMap.sourceAnchorChartMetric g x0)
      (Psi := Psi) (v := v) (V := Vs) (T := T)
      (by
        intro x y
        exact
          CovariantDerivative.chartMetric_symm g.inner
            (fun z a b => g.symm z a b) x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            x y)
      hRay hsmul horth a a'

/--
Target mixed block in the shape required by the corrected radial consumer,
derived from the target ray and the endpoint orthogonality feed.
-/
theorem target_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal
    (p0 : RoundSphere3)
    {Psi : E3 → ℝ → E3 × E3} {v Vt : E3} {T : ℝ}
    (hRay : (Psi v T).1 = T • Vt)
    (hsmul : ∀ (c : ℝ) (w : E3), (Psi (c • w) T).1 = c • (Psi w T).1)
    (horth :
      ∀ a : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) v)
            ((Psi (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) v a) T).1) Vt = 0)
    (a a' : E3) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) v)
        ((Psi (CartanPullback.radialPart
          (CartanMap.targetAnchorChartMetric p0) v a) T).1)
        ((Psi (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) v a') T).1) = 0 := by
  exact
    radialPart_endpoint_pairing_eq_zero_of_ray_and_transverse_orthogonal
      (G := CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) v))
      (B := CartanMap.targetAnchorChartMetric p0)
      (Psi := Psi) (v := v) (V := Vt) (T := T)
      (by
        intro x y
        exact
          CovariantDerivative.chartMetric_symm roundSphereMetric3.inner
            (fun z a b => roundSphereMetric3.symm z a b) p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) v)
            x y)
      hRay hsmul horth a a'

/--
One common feed into the corrected `T ^ 2` radial consumer.

This theorem is deliberately not curvature-only: it consumes the common
source/target ray, speed, endpoint-orthogonality, and transverse-pairing facts
at the same `(v, T, PsiS, PsiT, speed)` and feeds the verified consumer.
-/
theorem cartanMap_isLocalIsometry_of_common_ray_speed_orthogonal_transverse_feed
    {g : ClosedSmoothRiemannianMetric 3 M} {x0 : M} {p0 : RoundSphere3}
    (L : CartanMap.TangentAlignment g x0 p0)
    {v Vs Vt : E3} {A B : E3 ≃L[ℝ] E3}
    {PsiS PsiT : E3 → ℝ → E3 × E3} {speed T : ℝ}
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
    (hSourceTransverseOrthogonal :
      ∀ a : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1) Vs = 0)
    (hTargetTransverseOrthogonal :
      ∀ a : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1) Vt = 0)
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
  refine
    SpeedReconcile.cartanMap_isLocalIsometry_on_normalBall_of_ray_reconciled_decomposed_blocks
      (g := g) (x0 := x0) (p0 := p0) L
      (v := v) (Vs := Vs) (Vt := Vt) (A := A) (B := B)
      (PsiS := PsiS) (PsiT := PsiT) (speed := speed) (T := T)
      hA hB hvsrc hsourceDeriv htargetDeriv u u'
      hSourceRay hTargetRay hSourceEndpointSpeed hTargetEndpointSpeed
      hSourceAnchorSpeed hTargetAnchorSpeed
      ?_ hSourceTransverseTransverse ?_ hTargetTransverseTransverse
  · intro a a'
    exact
      source_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal
        (g := g) (x0 := x0) (Psi := PsiS) (v := v) (Vs := Vs) (T := T)
        hSourceRay hsmuls hSourceTransverseOrthogonal a a'
  · intro a a'
    exact
      target_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal
        (p0 := p0) (Psi := PsiT) (v := L v) (Vt := Vt) (T := T)
        hTargetRay hsmult hTargetTransverseOrthogonal a a'

end CombinedFeed
end Poincare
