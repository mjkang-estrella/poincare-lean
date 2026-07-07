import Poincare.Global.CorrectedRadial
import Poincare.Global.PairingUpgrade
import Poincare.Global.UnscaledFeed

/-!
# Pullback feed from decomposed endpoint blocks

This module isolates the exact scalar obstruction between the verified
decomposed endpoint blocks and the stronger anchor-pullback hypotheses consumed
by `PairingUpgrade`.

The campaign blocks assemble to a radial `timeRadialScale T` term and a
transverse `JacobiNormSystem.speedPinnedScale speed T` term.  The radial term
unscales to the anchor radial block whenever `T ≠ 0`; the transverse term
unscales to the anchor transverse block only under the explicit unit scalar

`JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1`.

The final theorem below feeds `PairingUpgrade` after this scalar has been
provided.  No hosted pullback identity is assumed.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace PullbackFeed

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

private theorem timeRadialScale_unscales (T : ℝ) (hT : T ≠ 0) :
    CorrectedRadial.timeRadialScale T * (T⁻¹ * T⁻¹) = 1 := by
  simp [CorrectedRadial.timeRadialScale, pow_two, hT, mul_assoc]

/--
Source exact anchor pullback from the verified time-radial/transverse block
assembly, after isolating the transverse unit-scalar normalization.
-/
theorem source_anchor_pullback_of_time_radial_blocks_and_unit_transverse
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {speed T : ℝ}
    (hv : v ≠ 0) (hT : T ≠ 0)
    (hTransverseUnit :
      JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1)
    (hadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψ (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1)
            ((Ψ (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v u') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v u'))
    (hRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψ (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1)
            ((Ψ (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u') T).1) = 0)
    (hTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψ (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1)
            ((Ψ (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u')) :
    ∀ u u' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ u T).1 (Ψ u' T).1 =
        CartanMap.sourceAnchorChartMetric g x₀ u u' := by
  intro u u'
  let S : E3 →L[ℝ] E3 →L[ℝ] ℝ := CartanMap.sourceAnchorChartMetric g x₀
  let r : E3 := CartanPullback.radialPart S v u
  let r' : E3 := CartanPullback.radialPart S v u'
  let t : E3 := CartanPullback.transversePart S v u
  let t' : E3 := CartanPullback.transversePart S v u'
  have hSplit :=
    CorrectedRadial.source_hosted_rescaled_endpoint_pairing_eq_of_time_radial_transverse_blocks
      (g := g) (x0 := x₀) (Psi := Ψ) (v := v) (T := T) (speed := speed)
      hadd hRadialRadial hRadialTransverse hTransverseTransverse u u'
  have hRadialUnit :
      CorrectedRadial.timeRadialScale T *
          S (T⁻¹ • r) (T⁻¹ • r') = S r r' := by
    rw [UnscaledFeed.sourceAnchorChartMetric_inv_smul_inv_smul]
    change CorrectedRadial.timeRadialScale T *
        ((T⁻¹ * T⁻¹) * S r r') = S r r'
    rw [← mul_assoc, timeRadialScale_unscales T hT]
    simp
  have hTransverseUnit' :
      JacobiNormSystem.speedPinnedScale speed T *
          S (T⁻¹ • t) (T⁻¹ • t') = S t t' := by
    rw [UnscaledFeed.sourceAnchorChartMetric_inv_smul_inv_smul]
    change JacobiNormSystem.speedPinnedScale speed T *
        ((T⁻¹ * T⁻¹) * S t t') = S t t'
    rw [← mul_assoc, hTransverseUnit]
    simp
  calc
    CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        (Ψ u T).1 (Ψ u' T).1 =
      CorrectedRadial.timeRadialScale T * S (T⁻¹ • r) (T⁻¹ • r') +
        JacobiNormSystem.speedPinnedScale speed T * S (T⁻¹ • t) (T⁻¹ • t') := by
        simpa [S, r, r', t, t'] using hSplit
    _ = S r r' + S t t' := by rw [hRadialUnit, hTransverseUnit']
    _ = S u u' := by
        simpa [S, r, r', t, t'] using
          (CartanPullback.sourceAnchorChartMetric_pair_eq_radial_add_transverse
            (g := g) (x₀ := x₀) hv u u').symm

/--
Target exact anchor pullback from the verified time-radial/transverse block
assembly, after isolating the same transverse unit-scalar normalization.
-/
theorem target_anchor_pullback_of_time_radial_blocks_and_unit_transverse
    (p₀ : RoundSphere3)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {speed T : ℝ}
    (hv : v ≠ 0) (hT : T ≠ 0)
    (hTransverseUnit :
      JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1)
    (hadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) v)
            ((Ψ (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) v u) T).1)
            ((Ψ (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) v u') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) v u'))
    (hRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) v)
            ((Ψ (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) v u) T).1)
            ((Ψ (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v u') T).1) = 0)
    (hTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) v)
            ((Ψ (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v u) T).1)
            ((Ψ (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) v u')) :
    ∀ u u' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) v)
          (Ψ u T).1 (Ψ u' T).1 =
        CartanMap.targetAnchorChartMetric p₀ u u' := by
  intro u u'
  let S : E3 →L[ℝ] E3 →L[ℝ] ℝ := CartanMap.targetAnchorChartMetric p₀
  let r : E3 := CartanPullback.radialPart S v u
  let r' : E3 := CartanPullback.radialPart S v u'
  let t : E3 := CartanPullback.transversePart S v u
  let t' : E3 := CartanPullback.transversePart S v u'
  have hSplit :=
    CorrectedRadial.target_hosted_rescaled_endpoint_pairing_eq_of_time_radial_transverse_blocks
      (p0 := p₀) (Psi := Ψ) (v := v) (T := T) (speed := speed)
      hadd hRadialRadial hRadialTransverse hTransverseTransverse u u'
  have hRadialUnit :
      CorrectedRadial.timeRadialScale T *
          S (T⁻¹ • r) (T⁻¹ • r') = S r r' := by
    rw [UnscaledFeed.targetAnchorChartMetric_inv_smul_inv_smul]
    change CorrectedRadial.timeRadialScale T *
        ((T⁻¹ * T⁻¹) * S r r') = S r r'
    rw [← mul_assoc, timeRadialScale_unscales T hT]
    simp
  have hTransverseUnit' :
      JacobiNormSystem.speedPinnedScale speed T *
          S (T⁻¹ • t) (T⁻¹ • t') = S t t' := by
    rw [UnscaledFeed.targetAnchorChartMetric_inv_smul_inv_smul]
    change JacobiNormSystem.speedPinnedScale speed T *
        ((T⁻¹ * T⁻¹) * S t t') = S t t'
    rw [← mul_assoc, hTransverseUnit]
    simp
  calc
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) v)
        (Ψ u T).1 (Ψ u' T).1 =
      CorrectedRadial.timeRadialScale T * S (T⁻¹ • r) (T⁻¹ • r') +
        JacobiNormSystem.speedPinnedScale speed T * S (T⁻¹ • t) (T⁻¹ • t') := by
        simpa [S, r, r', t, t'] using hSplit
    _ = S r r' + S t t' := by rw [hRadialUnit, hTransverseUnit']
    _ = S u u' := by
        simpa [S, r, r', t, t'] using
          (CartanPullback.targetAnchorChartMetric_pair_eq_radial_add_transverse
            (p₀ := p₀) hv u u').symm

/--
The complete `PairingUpgrade` feed once the selector-family block formulas
have been instantiated and the transverse unit scalar has been supplied.

This constructs the endpoint equivalences `A` and `B`, keeps their coercion
equalities to the selected `linearizedEndpointCLM`s, and feeds the final
hosted endpoint-pairing consumer.
-/
theorem exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_time_radial_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3} {Ψs Ψt : E3 → ℝ → E3 × E3} {speed T : ℝ}
    {hadds : ∀ w w' : E3,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E3),
      (Ψs (c • w) T).1 = c • (Ψs w T).1}
    {haddt : ∀ w w' : E3,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E3),
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
    (u u' : E3) (hv : v ≠ 0) (hLv : L v ≠ 0) (hT : T ≠ 0)
    (hTransverseUnit :
      JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1)
    (hSourceRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v a'))
    (hSourceRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) = 0)
    (hSourceTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v a'))
    (hTargetRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a'))
    (hTargetRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) = 0)
    (hTargetTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a')) :
    ∃ A B : E3 ≃L[ℝ] E3,
      (A : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls ∧
      (B : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult ∧
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
  have hSourcePullback :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          CartanMap.sourceAnchorChartMetric g x₀ a a' :=
    source_anchor_pullback_of_time_radial_blocks_and_unit_transverse
      (g := g) (x₀ := x₀) (Ψ := Ψs) (v := v) (speed := speed) (T := T)
      hv hT hTransverseUnit hadds
      hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
  have hTargetPullback :
      ∀ b b' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt b T).1 (Ψt b' T).1 =
          CartanMap.targetAnchorChartMetric p₀ b b' :=
    target_anchor_pullback_of_time_radial_blocks_and_unit_transverse
      (p₀ := p₀) (Ψ := Ψt) (v := L v) (speed := speed) (T := T)
      hLv hT hTransverseUnit haddt
      hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse
  exact
    PairingUpgrade.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_hosted_anchor_pullbacks
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (Ψs := Ψs) (Ψt := Ψt) (T := T)
      hvsrc hsourceDeriv htargetDeriv u u' hSourcePullback hTargetPullback

end PullbackFeed
end Poincare
