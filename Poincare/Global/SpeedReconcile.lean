import Poincare.Global.RayIdentification

/-!
# Speed-square reconciliation for radial blocks

`RayIdentification` exports the radial endpoint pairing in coefficient-product
form.  The speed-free `CorrectedRadial.timeRadialScale` consumer wants the same
fact in rescaled-anchor form.  This module proves the algebraic conversion.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace SpeedReconcile

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

/--
The scalar bookkeeping behind the reconciliation:

`ρρ' * (T² * speed²) = T² * (ρρ' * speed²)`.

The right-hand factor `ρρ' * speed²` is exactly the rescaled-anchor radial
pairing once `B (T⁻¹ • v) (T⁻¹ • v) = speed²`.
-/
theorem radialCoeff_mul_plainRadialScale_eq_timeRadialScale_mul_rescaled_radialPart_pair
    (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) {v : E3} {speed T : ℝ}
    (hanchorSpeed : B (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2) (u u' : E3) :
    (CartanPullback.radialCoeff B v u * CartanPullback.radialCoeff B v u') *
        CorrectedRadial.plainRadialScale speed T =
      CorrectedRadial.timeRadialScale T *
        B (T⁻¹ • CartanPullback.radialPart B v u)
          (T⁻¹ • CartanPullback.radialPart B v u') := by
  have hscaled :
      B (T⁻¹ • CartanPullback.radialPart B v u)
          (T⁻¹ • CartanPullback.radialPart B v u') =
        (CartanPullback.radialCoeff B v u *
            CartanPullback.radialCoeff B v u') * speed ^ 2 := by
    calc
      B (T⁻¹ • CartanPullback.radialPart B v u)
          (T⁻¹ • CartanPullback.radialPart B v u') =
        B (CartanPullback.radialCoeff B v u • (T⁻¹ • v))
          (CartanPullback.radialCoeff B v u' • (T⁻¹ • v)) := by
          simp [CartanPullback.radialPart, smul_smul, mul_assoc, mul_left_comm,
            mul_comm]
      _ =
        (CartanPullback.radialCoeff B v u *
            CartanPullback.radialCoeff B v u') *
          B (T⁻¹ • v) (T⁻¹ • v) := by
          simp [mul_assoc, mul_left_comm]
      _ =
        (CartanPullback.radialCoeff B v u *
            CartanPullback.radialCoeff B v u') * speed ^ 2 := by
          rw [hanchorSpeed]
  rw [hscaled]
  dsimp [CorrectedRadial.plainRadialScale, CorrectedRadial.timeRadialScale]
  ring

/--
Ray-identification radial pairing rewritten in the speed-free consumer form.
-/
theorem radialPart_endpoint_pairing_eq_timeRadialScale_mul_rescaled_radialPart_pair
    (G B : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    {Psi : E3 → ℝ → E3 × E3} {v V : E3} {T speed : ℝ}
    (hRay : (Psi v T).1 = T • V)
    (hsmul : ∀ (c : ℝ) (w : E3), (Psi (c • w) T).1 = c • (Psi w T).1)
    (hendpointSpeed : G V V = speed ^ 2)
    (hanchorSpeed : B (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2) (u u' : E3) :
    G ((Psi (CartanPullback.radialPart B v u) T).1)
      ((Psi (CartanPullback.radialPart B v u') T).1) =
        CorrectedRadial.timeRadialScale T *
          B (T⁻¹ • CartanPullback.radialPart B v u)
            (T⁻¹ • CartanPullback.radialPart B v u') := by
  calc
    G ((Psi (CartanPullback.radialPart B v u) T).1)
        ((Psi (CartanPullback.radialPart B v u') T).1) =
      (CartanPullback.radialCoeff B v u *
          CartanPullback.radialCoeff B v u') *
        CorrectedRadial.plainRadialScale speed T :=
        RayIdentification.radialPart_endpoint_pairing_eq_radialCoeff_mul_plainRadialScale
          (G := G) (B := B) (Ψ := Psi) (v := v) (V := V)
          (T := T) (speed := speed) hRay hsmul hendpointSpeed u u'
    _ =
        CorrectedRadial.timeRadialScale T *
          B (T⁻¹ • CartanPullback.radialPart B v u)
            (T⁻¹ • CartanPullback.radialPart B v u') :=
        radialCoeff_mul_plainRadialScale_eq_timeRadialScale_mul_rescaled_radialPart_pair
          (B := B) (v := v) (speed := speed) (T := T) hanchorSpeed u u'

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/-- Source radial block supplied by ray identification and speed-package equalities. -/
theorem source_radialPart_endpoint_pairing_eq_timeRadialScale
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {Psi : E3 → ℝ → E3 × E3} {v V : E3} {T speed : ℝ}
    (hRay : (Psi v T).1 = T • V)
    (hsmul : ∀ (c : ℝ) (w : E3), (Psi (c • w) T).1 = c • (Psi w T).1)
    (hendpointSpeed :
      CovariantDerivative.chartMetric g.inner x0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
          V V = speed ^ 2)
    (hanchorSpeed :
      CartanMap.sourceAnchorChartMetric g x0 (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (u u' : E3) :
    CovariantDerivative.chartMetric g.inner x0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
        ((Psi (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x0) v u) T).1)
        ((Psi (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x0) v u') T).1) =
      CorrectedRadial.timeRadialScale T *
        CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v u') :=
  radialPart_endpoint_pairing_eq_timeRadialScale_mul_rescaled_radialPart_pair
    (G := CovariantDerivative.chartMetric g.inner x0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v))
    (B := CartanMap.sourceAnchorChartMetric g x0)
    (Psi := Psi) (v := v) (V := V) (T := T) (speed := speed)
    hRay hsmul hendpointSpeed hanchorSpeed u u'

/-- Target radial block supplied by ray identification and speed-package equalities. -/
theorem target_radialPart_endpoint_pairing_eq_timeRadialScale
    (p0 : RoundSphere3)
    {Psi : E3 → ℝ → E3 × E3} {v V : E3} {T speed : ℝ}
    (hRay : (Psi v T).1 = T • V)
    (hsmul : ∀ (c : ℝ) (w : E3), (Psi (c • w) T).1 = c • (Psi w T).1)
    (hendpointSpeed :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0) v)
          V V = speed ^ 2)
    (hanchorSpeed :
      CartanMap.targetAnchorChartMetric p0 (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (u u' : E3) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) v)
        ((Psi (CartanPullback.radialPart
          (CartanMap.targetAnchorChartMetric p0) v u) T).1)
        ((Psi (CartanPullback.radialPart
          (CartanMap.targetAnchorChartMetric p0) v u') T).1) =
      CorrectedRadial.timeRadialScale T *
        CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) v u') :=
  radialPart_endpoint_pairing_eq_timeRadialScale_mul_rescaled_radialPart_pair
    (G := CovariantDerivative.chartMetric roundSphereMetric3.inner p0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p0) v))
    (B := CartanMap.targetAnchorChartMetric p0)
    (Psi := Psi) (v := v) (V := V) (T := T) (speed := speed)
    hRay hsmul hendpointSpeed hanchorSpeed u u'

/--
Final local-isometry consumer with radial blocks discharged by the reconciliation
lemma.  The remaining hypotheses are the non-radial endpoint blocks and the
honest source/target ray-speed equalities; no radial block is assumed.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_ray_reconciled_decomposed_blocks
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
    (hSourceRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) = 0)
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
    (hTargetRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) = 0)
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
    CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_time_radial_decomposed_blocks
      (g := g) (x0 := x0) (p0 := p0) L
      (v := v) (A := A) (B := B) (PsiS := PsiS) (PsiT := PsiT)
      (speed := speed) (T := T)
      hA hB hvsrc hsourceDeriv htargetDeriv u u'
      ?_ hSourceRadialTransverse hSourceTransverseTransverse
      ?_ hTargetRadialTransverse hTargetTransverseTransverse
  · intro a a'
    exact
      source_radialPart_endpoint_pairing_eq_timeRadialScale
        (g := g) (x0 := x0) (Psi := PsiS) (v := v) (V := Vs)
        (T := T) (speed := speed)
        hSourceRay hsmuls hSourceEndpointSpeed hSourceAnchorSpeed a a'
  · intro a a'
    exact
      target_radialPart_endpoint_pairing_eq_timeRadialScale
        (p0 := p0) (Psi := PsiT) (v := L v) (V := Vt)
        (T := T) (speed := speed)
        hTargetRay hsmult hTargetEndpointSpeed hTargetAnchorSpeed a a'

end SpeedReconcile
end Poincare
