import Poincare.Global.CartanPullback
import Poincare.Global.SpeedGeneric

/-!
# Decomposed hosted endpoint assembly

This module contains the radial/transverse endpoint-pairing assembly needed
after the all-direction `horth` route was refuted.  The main algebraic lemma
takes the three genuine blocks at the anchor radial decomposition:

* radial/radial,
* radial/transverse, and
* transverse/transverse,

and reconstructs the full hosted endpoint pairing for arbitrary input
directions by endpoint additivity and bilinearity.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace DecomposedAssembly

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

/--
Radial/transverse block assembly for one hosted endpoint family.

The vector `u` is split using the anchor bilinear form `S` and radial vector
`v`.  Additivity of the endpoint map expands `Ψ u`; bilinearity of `G` expands
the endpoint pairing; the mixed endpoint block and the mixed anchor blocks
vanish by hypothesis and by the Gram algebra from `CartanPullback`.
-/
theorem hosted_rescaled_endpoint_pairing_eq_of_radial_transverse_blocks
    (G S : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T κ : ℝ}
    (hGsymm : ∀ x y : E3, G x y = G y x)
    (hSsymm : ∀ x y : E3, S x y = S y x)
    (hSvv : S v v ≠ 0)
    (hadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hRadialRadial :
      ∀ u u' : E3,
        G ((Ψ (CartanPullback.radialPart S v u) T).1)
          ((Ψ (CartanPullback.radialPart S v u') T).1) =
          κ *
            S (T⁻¹ • CartanPullback.radialPart S v u)
              (T⁻¹ • CartanPullback.radialPart S v u'))
    (hRadialTransverse :
      ∀ u u' : E3,
        G ((Ψ (CartanPullback.radialPart S v u) T).1)
          ((Ψ (CartanPullback.transversePart S v u') T).1) = 0)
    (hTransverseTransverse :
      ∀ u u' : E3,
        G ((Ψ (CartanPullback.transversePart S v u) T).1)
          ((Ψ (CartanPullback.transversePart S v u') T).1) =
          κ *
            S (T⁻¹ • CartanPullback.transversePart S v u)
              (T⁻¹ • CartanPullback.transversePart S v u')) :
    ∀ u u' : E3,
      G ((Ψ u T).1) ((Ψ u' T).1) =
        κ * S (T⁻¹ • u) (T⁻¹ • u') := by
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
  have hΨu : (Ψ u T).1 = (Ψ r T).1 + (Ψ t T).1 := by
    rw [hu]
    exact hadd r t
  have hΨu' : (Ψ u' T).1 = (Ψ r' T).1 + (Ψ t' T).1 := by
    rw [hu']
    exact hadd r' t'
  have hrr :
      G ((Ψ r T).1) ((Ψ r' T).1) =
        κ * S (T⁻¹ • r) (T⁻¹ • r') := by
    simpa [r, r'] using hRadialRadial u u'
  have hrt :
      G ((Ψ r T).1) ((Ψ t' T).1) = 0 := by
    simpa [r, t'] using hRadialTransverse u u'
  have htr :
      G ((Ψ t T).1) ((Ψ r' T).1) = 0 := by
    have hsymm :
        G ((Ψ t T).1) ((Ψ r' T).1) =
          G ((Ψ r' T).1) ((Ψ t T).1) :=
      hGsymm (Ψ t T).1 (Ψ r' T).1
    have hzero :
        G ((Ψ r' T).1) ((Ψ t T).1) = 0 := by
      simpa [r', t] using hRadialTransverse u' u
    exact hsymm.trans hzero
  have htt :
      G ((Ψ t T).1) ((Ψ t' T).1) =
        κ * S (T⁻¹ • t) (T⁻¹ • t') := by
    simpa [t, t'] using hTransverseTransverse u u'
  have hSrt' : S (T⁻¹ • r) (T⁻¹ • t') = 0 := by
    simp [r, t', CartanPullback.radialPart_transversePart_pair
      (B := S) (v := v) (u := u) (u' := u') hSsymm hSvv]
  have hStr' : S (T⁻¹ • t) (T⁻¹ • r') = 0 := by
    simp [r', t, CartanPullback.transversePart_radialPart_pair
      (B := S) (v := v) (u := u) (u' := u') hSvv]
  have hSscaled :
      S (T⁻¹ • u) (T⁻¹ • u') =
        S (T⁻¹ • r) (T⁻¹ • r') + S (T⁻¹ • t) (T⁻¹ • t') := by
    calc
      S (T⁻¹ • u) (T⁻¹ • u') =
          S (T⁻¹ • (r + t)) (T⁻¹ • (r' + t')) := by rw [hu, hu']
      _ = S (T⁻¹ • r + T⁻¹ • t) (T⁻¹ • r' + T⁻¹ • t') := by
          simp [smul_add]
      _ = S (T⁻¹ • r) (T⁻¹ • r') + S (T⁻¹ • t) (T⁻¹ • t') := by
          simp only [map_add, ContinuousLinearMap.add_apply, hSrt', hStr',
            zero_add, add_zero]
  calc
    G ((Ψ u T).1) ((Ψ u' T).1) =
        G ((Ψ r T).1 + (Ψ t T).1) ((Ψ r' T).1 + (Ψ t' T).1) := by
          rw [hΨu, hΨu']
    _ = G ((Ψ r T).1) ((Ψ r' T).1) +
        G ((Ψ r T).1) ((Ψ t' T).1) +
        G ((Ψ t T).1) ((Ψ r' T).1) +
        G ((Ψ t T).1) ((Ψ t' T).1) := by
          simp only [map_add, ContinuousLinearMap.add_apply]
          ring
    _ = κ * S (T⁻¹ • r) (T⁻¹ • r') + 0 + 0 +
        κ * S (T⁻¹ • t) (T⁻¹ • t') := by
          rw [hrr, hrt, htr, htt]
    _ = κ * (S (T⁻¹ • r) (T⁻¹ • r') + S (T⁻¹ • t) (T⁻¹ • t')) := by
          ring
    _ = κ * S (T⁻¹ • u) (T⁻¹ • u') := by
          rw [hSscaled]

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Source hosted endpoint assembly specialized to the source endpoint and anchor
chart metrics.
-/
theorem source_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T κ : ℝ} (hv : v ≠ 0)
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
          κ * CartanMap.sourceAnchorChartMetric g x₀
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
          κ * CartanMap.sourceAnchorChartMetric g x₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u')) :
    ∀ u u' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ u T).1 (Ψ u' T).1 =
        κ * CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • u) (T⁻¹ • u') :=
  hosted_rescaled_endpoint_pairing_eq_of_radial_transverse_blocks
    (G := CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v))
    (S := CartanMap.sourceAnchorChartMetric g x₀)
    (Ψ := Ψ) (v := v) (T := T) (κ := κ)
    (by
      intro x y
      exact
        CovariantDerivative.chartMetric_symm g.inner
          (fun z a b => g.symm z a b) x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          x y)
    (CartanMap.sourceAnchorChartMetric_symm g x₀)
    (CartanPullback.sourceAnchorChartMetric_self_ne_zero (g := g) (x₀ := x₀) hv)
    hadd hRadialRadial hRadialTransverse hTransverseTransverse

/--
Target hosted endpoint assembly specialized to the round-sphere endpoint and
anchor chart metrics.
-/
theorem target_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
    (p₀ : RoundSphere3)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T κ : ℝ} (hv : v ≠ 0)
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
          κ * CartanMap.targetAnchorChartMetric p₀
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
          κ * CartanMap.targetAnchorChartMetric p₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v u)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v u')) :
    ∀ u u' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) v)
          (Ψ u T).1 (Ψ u' T).1 =
        κ * CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • u) (T⁻¹ • u') :=
  hosted_rescaled_endpoint_pairing_eq_of_radial_transverse_blocks
    (G := CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) v))
    (S := CartanMap.targetAnchorChartMetric p₀)
    (Ψ := Ψ) (v := v) (T := T) (κ := κ)
    (by
      intro x y
      exact
        CovariantDerivative.chartMetric_symm roundSphereMetric3.inner
          (fun z a b => roundSphereMetric3.symm z a b) p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) v)
          x y)
    (CartanMap.targetAnchorChartMetric_symm p₀)
    (CartanPullback.targetAnchorChartMetric_self_ne_zero (p₀ := p₀) hv)
    hadd hRadialRadial hRadialTransverse hTransverseTransverse

/--
Common-speed endpoint feed obtained by decomposed source and target block
assemblies.
-/
theorem hosted_endpoint_pairing_feed_of_common_speed_decomposed_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3} {Ψs Ψt : E3 → ℝ → E3 × E3} {speed T : ℝ}
    (hv : v ≠ 0) (hLv : L v ≠ 0) (hspeed : speed ≠ 0) (hT : T ≠ 0)
    (hadds : ∀ w w' : E3,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1)
    (haddt : ∀ w w' : E3,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1)
    (hSourceRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v u'))
    (hSourceRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u') T).1) = 0)
    (hSourceTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u'))
    (hTargetRadialRadial :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) u) T).1)
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) u)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) u'))
    (hTargetRadialTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) u) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) u') T).1) = 0)
    (hTargetTransverseTransverse :
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) u) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) u') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) u)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) u')) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) T).1 (Ψt (L a') T).1 =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 := by
  have hSourceRescaled :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a') :=
    source_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
      (g := g) (x₀ := x₀) (Ψ := Ψs) (v := v) (T := T)
      (κ := JacobiNormSystem.speedPinnedScale speed T) hv hadds
      hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
  have hTargetRescaled :
      ∀ w w' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w T).1 (Ψt w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') :=
    target_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
      (p₀ := p₀) (Ψ := Ψt) (v := L v) (T := T)
      (κ := JacobiNormSystem.speedPinnedScale speed T) hLv haddt
      hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse
  exact
    SpeedGeneric.hosted_endpoint_pairing_feed_of_common_speed_rescaled_anchor_pairings
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (Ψs := Ψs) (Ψt := Ψt) (speed := speed) (T := T)
      hspeed hT hSourceRescaled hTargetRescaled

/--
Final Cartan local-isometry consumer fed by the decomposed common-speed
endpoint assembly.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_common_speed_decomposed_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3} {A B : E3 ≃L[ℝ] E3}
    {Ψs Ψt : E3 → ℝ → E3 × E3} {speed T : ℝ}
    {hadds : ∀ w w' : E3,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E3),
      (Ψs (c • w) T).1 = c • (Ψs w T).1}
    {haddt : ∀ w w' : E3,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E3),
      (Ψt (c • w) T).1 = c • (Ψt w T).1}
    (hA :
      (A : E3 →L[ℝ] E3) =
        linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls)
    (hB :
      (B : E3 →L[ℝ] E3) =
        linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult)
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E3 →L[ℝ] E3) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E3 →L[ℝ] E3) (L v))
    (u u' : E3) (hv : v ≠ 0) (hLv : L v ≠ 0)
    (hspeed : speed ≠ 0) (hT : T ≠ 0)
    (hSourceRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
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
          JacobiNormSystem.speedPinnedScale speed T *
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
  have hSourceRescaled :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a') :=
    source_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
      (g := g) (x₀ := x₀) (Ψ := Ψs) (v := v) (T := T)
      (κ := JacobiNormSystem.speedPinnedScale speed T) hv hadds
      hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
  have hTargetRescaled :
      ∀ w w' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w T).1 (Ψt w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') :=
    target_hosted_rescaled_endpoint_pairing_eq_of_decomposed_blocks
      (p₀ := p₀) (Ψ := Ψt) (v := L v) (T := T)
      (κ := JacobiNormSystem.speedPinnedScale speed T) hLv haddt
      hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse
  exact
    SpeedGeneric.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_rescaled_anchor_pairings
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (A := A) (B := B) (Ψs := Ψs) (Ψt := Ψt)
      (speed := speed) (T := T)
      hA hB hvsrc hsourceDeriv htargetDeriv u u' hspeed hT
      hSourceRescaled hTargetRescaled

end DecomposedAssembly
end Poincare
