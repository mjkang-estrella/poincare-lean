import Poincare.Global.BlocksDischarge
import Poincare.Global.PairingFeed

/-!
# Corrected radial consumer

This module adds the hosted decomposed consumer with the radial/radial scalar
separated from the transverse sine scalar.  The radial block uses the plain
ray time-speed scale, while the transverse block keeps
`JacobiNormSystem.speedPinnedScale`.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CorrectedRadial

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

/-- Plain radial ray scale: the radial endpoint variation scales by time and speed. -/
def plainRadialScale (speed T : ℝ) : ℝ :=
  T ^ 2 * speed ^ 2

/-- The corrected radial scale unfolds to the ordinary time-speed square. -/
theorem plainRadialScale_unfold (speed T : ℝ) :
    plainRadialScale speed T = T ^ 2 * speed ^ 2 := by
  rfl

/--
For rescaled initial data, the corrected radial scalar removes the inverse
time factors and leaves only the speed square.
-/
theorem plainRadialScale_rescaled_pairing
    (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) {speed T : ℝ} (hT : T ≠ 0) (w w' : E3) :
    plainRadialScale speed T * B (T⁻¹ • w) (T⁻¹ • w') =
      speed ^ 2 * B w w' := by
  simp [plainRadialScale, hT, pow_two, mul_assoc, mul_left_comm, mul_comm]

/--
Radial/transverse hosted endpoint assembly with independent radial and
transverse scalars.
-/
theorem hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks
    (G S : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    {Psi : E3 → ℝ → E3 × E3} {v : E3} {T radialScale transverseScale : ℝ}
    (hGsymm : ∀ x y : E3, G x y = G y x)
    (hadd : ∀ w w' : E3,
      (Psi (w + w') T).1 = (Psi w T).1 + (Psi w' T).1)
    (hRadialRadial :
      ∀ u u' : E3,
        G ((Psi (CartanPullback.radialPart S v u) T).1)
          ((Psi (CartanPullback.radialPart S v u') T).1) =
          radialScale *
            S (T⁻¹ • CartanPullback.radialPart S v u)
              (T⁻¹ • CartanPullback.radialPart S v u'))
    (hRadialTransverse :
      ∀ u u' : E3,
        G ((Psi (CartanPullback.radialPart S v u) T).1)
          ((Psi (CartanPullback.transversePart S v u') T).1) = 0)
    (hTransverseTransverse :
      ∀ u u' : E3,
        G ((Psi (CartanPullback.transversePart S v u) T).1)
          ((Psi (CartanPullback.transversePart S v u') T).1) =
          transverseScale *
            S (T⁻¹ • CartanPullback.transversePart S v u)
              (T⁻¹ • CartanPullback.transversePart S v u')) :
    ∀ u u' : E3,
      G ((Psi u T).1) ((Psi u' T).1) =
        radialScale *
            S (T⁻¹ • CartanPullback.radialPart S v u)
              (T⁻¹ • CartanPullback.radialPart S v u') +
          transverseScale *
            S (T⁻¹ • CartanPullback.transversePart S v u)
              (T⁻¹ • CartanPullback.transversePart S v u') := by
  intro u u'
  let r : E3 := CartanPullback.radialPart S v u
  let t : E3 := CartanPullback.transversePart S v u
  let r' : E3 := CartanPullback.radialPart S v u'
  let t' : E3 := CartanPullback.transversePart S v u'
  have hu : u = r + t := by
    show u = CartanPullback.radialPart S v u + CartanPullback.transversePart S v u
    rw [CartanPullback.radialPart_add_transversePart]
  have hu' : u' = r' + t' := by
    show u' =
      CartanPullback.radialPart S v u' + CartanPullback.transversePart S v u'
    rw [CartanPullback.radialPart_add_transversePart]
  have hPsiu : (Psi u T).1 = (Psi r T).1 + (Psi t T).1 := by
    rw [hu]
    exact hadd r t
  have hPsiu' : (Psi u' T).1 = (Psi r' T).1 + (Psi t' T).1 := by
    rw [hu']
    exact hadd r' t'
  have hrr :
      G ((Psi r T).1) ((Psi r' T).1) =
        radialScale * S (T⁻¹ • r) (T⁻¹ • r') := by
    simpa [r, r'] using hRadialRadial u u'
  have hrt :
      G ((Psi r T).1) ((Psi t' T).1) = 0 := by
    simpa [r, t'] using hRadialTransverse u u'
  have htr :
      G ((Psi t T).1) ((Psi r' T).1) = 0 := by
    have hsymm :
        G ((Psi t T).1) ((Psi r' T).1) =
          G ((Psi r' T).1) ((Psi t T).1) :=
      hGsymm (Psi t T).1 (Psi r' T).1
    have hzero :
        G ((Psi r' T).1) ((Psi t T).1) = 0 := by
      simpa [r', t] using hRadialTransverse u' u
    exact hsymm.trans hzero
  have htt :
      G ((Psi t T).1) ((Psi t' T).1) =
        transverseScale * S (T⁻¹ • t) (T⁻¹ • t') := by
    simpa [t, t'] using hTransverseTransverse u u'
  calc
    G ((Psi u T).1) ((Psi u' T).1) =
        G ((Psi r T).1 + (Psi t T).1) ((Psi r' T).1 + (Psi t' T).1) := by
          rw [hPsiu, hPsiu']
    _ = G ((Psi r T).1) ((Psi r' T).1) +
        G ((Psi r T).1) ((Psi t' T).1) +
        G ((Psi t T).1) ((Psi r' T).1) +
        G ((Psi t T).1) ((Psi t' T).1) := by
          simp only [map_add, ContinuousLinearMap.add_apply]
          ring
    _ = radialScale * S (T⁻¹ • r) (T⁻¹ • r') + 0 + 0 +
        transverseScale * S (T⁻¹ • t) (T⁻¹ • t') := by
          rw [hrr, hrt, htr, htt]
    _ = radialScale * S (T⁻¹ • r) (T⁻¹ • r') +
        transverseScale * S (T⁻¹ • t) (T⁻¹ • t') := by
          ring
    _ =
        radialScale *
            S (T⁻¹ • CartanPullback.radialPart S v u)
              (T⁻¹ • CartanPullback.radialPart S v u') +
          transverseScale *
            S (T⁻¹ • CartanPullback.transversePart S v u)
              (T⁻¹ • CartanPullback.transversePart S v u') := by
          simp [r, t, r', t']

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/-- Source endpoint assembly with the corrected radial scalar. -/
theorem source_hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {Psi : E3 → ℝ → E3 × E3} {v : E3} {T speed : ℝ}
    (hadd : ∀ w w' : E3,
      (Psi (w + w') T).1 = (Psi w T).1 + (Psi w' T).1)
    (hRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((Psi (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v u) T).1)
            ((Psi (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v u') T).1) =
          plainRadialScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v u'))
    (hRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((Psi (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v u) T).1)
            ((Psi (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v u') T).1) = 0)
    (hTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((Psi (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v u) T).1)
            ((Psi (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v u')) :
    ∀ u u' : E3,
      CovariantDerivative.chartMetric g.inner x0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
          (Psi u T).1 (Psi u' T).1 =
        plainRadialScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v u') +
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v u') :=
  hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks
    (G := CovariantDerivative.chartMetric g.inner x0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v))
    (S := CartanMap.sourceAnchorChartMetric g x0)
    (Psi := Psi) (v := v) (T := T)
    (radialScale := plainRadialScale speed T)
    (transverseScale := JacobiNormSystem.speedPinnedScale speed T)
    (by
      intro x y
      exact
        CovariantDerivative.chartMetric_symm g.inner
          (fun z a b => g.symm z a b) x0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
          x y)
    hadd hRadialRadial hRadialTransverse hTransverseTransverse

/-- Target endpoint assembly with the corrected radial scalar. -/
theorem target_hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks
    (p0 : RoundSphere3)
    {Psi : E3 → ℝ → E3 × E3} {v : E3} {T speed : ℝ}
    (hadd : ∀ w w' : E3,
      (Psi (w + w') T).1 = (Psi w T).1 + (Psi w' T).1)
    (hRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) v)
            ((Psi (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) v u) T).1)
            ((Psi (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) v u') T).1) =
          plainRadialScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) v u'))
    (hRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) v)
            ((Psi (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) v u) T).1)
            ((Psi (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) v u') T).1) = 0)
    (hTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) v)
            ((Psi (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) v u) T).1)
            ((Psi (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) v u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) v u')) :
    ∀ u u' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0) v)
          (Psi u T).1 (Psi u' T).1 =
        plainRadialScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) v u') +
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) v u') :=
  hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks
    (G := CovariantDerivative.chartMetric roundSphereMetric3.inner p0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p0) v))
    (S := CartanMap.targetAnchorChartMetric p0)
    (Psi := Psi) (v := v) (T := T)
    (radialScale := plainRadialScale speed T)
    (transverseScale := JacobiNormSystem.speedPinnedScale speed T)
    (by
      intro x y
      exact
        CovariantDerivative.chartMetric_symm roundSphereMetric3.inner
          (fun z a b => roundSphereMetric3.symm z a b) p0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0) v)
          x y)
    hadd hRadialRadial hRadialTransverse hTransverseTransverse

/--
Common-speed endpoint feed from corrected source and target decomposed blocks.
The radial and transverse anchor summands match separately through the tangent
alignment.
-/
theorem hosted_endpoint_pairing_feed_of_common_speed_corrected_radial_decomposed_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x0 : M} {p0 : RoundSphere3}
    (L : CartanMap.TangentAlignment g x0 p0)
    {v : E3} {PsiS PsiT : E3 → ℝ → E3 × E3} {speed T : ℝ}
    (hadds : ∀ w w' : E3,
      (PsiS (w + w') T).1 = (PsiS w T).1 + (PsiS w' T).1)
    (haddt : ∀ w w' : E3,
      (PsiT (w + w') T).1 = (PsiT w T).1 + (PsiT w' T).1)
    (hSourceRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v u) T).1)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v u') T).1) =
          plainRadialScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v u'))
    (hSourceRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v u) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v u') T).1) = 0)
    (hSourceTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v u) T).1)
            ((PsiS (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x0) v u'))
    (hTargetRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) u) T).1)
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) u') T).1) =
          plainRadialScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) u'))
    (hTargetRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) u) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) u') T).1) = 0)
    (hTargetTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) u) T).1)
            ((PsiT (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p0) (L v) u')) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p0) (L v))
          (PsiT (L a) T).1 (PsiT (L a') T).1 =
        CovariantDerivative.chartMetric g.inner x0
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
          (PsiS a T).1 (PsiS a' T).1 := by
  have hSourceSplit :=
    source_hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks
      (g := g) (x0 := x0) (Psi := PsiS) (v := v) (T := T) (speed := speed)
      hadds hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
  have hTargetSplit :=
    target_hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks
      (p0 := p0) (Psi := PsiT) (v := L v) (T := T) (speed := speed)
      haddt hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse
  intro a a'
  have hRadialAnchor :
      CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) (L v) (L a))
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) (L v) (L a')) =
        CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v a)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v a') := by
    simpa [CartanPullback.tangentAlignment_radialPart_map] using
      CartanMap.TangentAlignment.map_app L
        (T⁻¹ • CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x0) v a)
        (T⁻¹ • CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x0) v a')
  have hTransverseAnchor :
      CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) (L v) (L a))
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) (L v) (L a')) =
        CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a') := by
    simpa [CartanPullback.tangentAlignment_transversePart_map] using
      CartanMap.TangentAlignment.map_app L
        (T⁻¹ • CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a)
        (T⁻¹ • CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a')
  calc
    CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) (L v))
        (PsiT (L a) T).1 (PsiT (L a') T).1 =
      plainRadialScale speed T *
          CartanMap.targetAnchorChartMetric p0
            (T⁻¹ • CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) (L a))
            (T⁻¹ • CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) (L a')) +
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p0
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) (L a))
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p0) (L v) (L a')) :=
        hTargetSplit (L a) (L a')
    _ =
      plainRadialScale speed T *
          CartanMap.sourceAnchorChartMetric g x0
            (T⁻¹ • CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a)
            (T⁻¹ • CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a') +
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x0
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x0) v a') := by
        rw [hRadialAnchor, hTransverseAnchor]
    _ =
      CovariantDerivative.chartMetric g.inner x0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
        (PsiS a T).1 (PsiS a' T).1 := (hSourceSplit a a').symm

/--
Final Cartan local-isometry consumer fed by corrected-radial decomposed source
and target endpoint blocks.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_common_speed_corrected_radial_decomposed_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x0 : M} {p0 : RoundSphere3}
    (L : CartanMap.TangentAlignment g x0 p0)
    {v : E3} {A B : E3 ≃L[ℝ] E3}
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
    (hSourceRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
            ((PsiS (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
          plainRadialScale speed T *
            CartanMap.sourceAnchorChartMetric g x0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x0) v a'))
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
    (hTargetRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0) (L v))
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
            ((PsiT (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
          plainRadialScale speed T *
            CartanMap.targetAnchorChartMetric p0
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p0) (L v) a'))
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
    PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed
      (g := g) (x₀ := x0) (p₀ := p0) L
      (v := v) (A := A) (B := B) (Ψs := PsiS) (Ψt := PsiT)
      (Ts := T) (Tt := T)
      hA hB hvsrc hsourceDeriv htargetDeriv u u' ?_
  exact
    hosted_endpoint_pairing_feed_of_common_speed_corrected_radial_decomposed_blocks
      (g := g) (x0 := x0) (p0 := p0) L
      (v := v) (PsiS := PsiS) (PsiT := PsiT) (speed := speed) (T := T)
      hadds haddt
      hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
      hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse

end CorrectedRadial
end Poincare
