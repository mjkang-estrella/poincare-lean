import Poincare.Global.ScaledUpgrade
import Poincare.Global.PullbackFeed
import Poincare.Global.ScalarPin

/-!
# Sine-square pullback instantiation boundary

`ScaledUpgrade.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pullbacks`
constructs the endpoint equivalences once each hosted endpoint family has a
full sine-square pullback against its anchor metric.

The corrected selector-level blocks do not have that shape: the radial block
uses the plain time-radial scale, while the transverse block uses the
speed-pinned sine scale.  This file isolates the precise obstruction.  A full
`sin²` pullback combined with the actual time-radial block forces
`sin² = 1` on the radial line.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace SinSqInstantiate

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

theorem radialPart_self_of_self_ne_zero
    {S : E3 →L[ℝ] E3 →L[ℝ] ℝ} {v : E3} (hSvv : S v v ≠ 0) :
    CartanPullback.radialPart S v v = v := by
  simp [CartanPullback.radialPart, CartanPullback.radialCoeff, hSvv]

theorem continuousLinearPairing_inv_smul_inv_smul
    (S : E3 →L[ℝ] E3 →L[ℝ] ℝ) (T : ℝ) (u v : E3) :
    S (T⁻¹ • u) (T⁻¹ • v) = (T⁻¹ * T⁻¹) * S u v := by
  have hleft : S (T⁻¹ • u) = T⁻¹ • S u := by
    exact map_smul S T⁻¹ u
  have hright : (S u) (T⁻¹ • v) = T⁻¹ * S u v := by
    simp [map_smul (S u) T⁻¹ v]
  calc
    S (T⁻¹ • u) (T⁻¹ • v) = (T⁻¹ • S u) (T⁻¹ • v) := by rw [hleft]
    _ = T⁻¹ * (S u (T⁻¹ • v)) := by rfl
    _ = T⁻¹ * (T⁻¹ * S u v) := by rw [hright]
    _ = (T⁻¹ * T⁻¹) * S u v := by ring

theorem timeRadialScale_mul_inv_sq (T : ℝ) (hT : T ≠ 0) :
    CorrectedRadial.timeRadialScale T * (T⁻¹ * T⁻¹) = 1 := by
  simp [CorrectedRadial.timeRadialScale, pow_two, hT, mul_assoc]

/--
The exact obstruction to feeding the corrected radial block into the
full-scalar sine-square upgrade: on the radial vector itself, the actual
time-radial block is unscaled, so a full `sin²` pullback would force
`Real.sin θ ^ 2 = 1`.
-/
theorem time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
    {G S : E3 →L[ℝ] E3 →L[ℝ] ℝ}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T θ : ℝ}
    (hSvv : S v v ≠ 0) (hT : T ≠ 0)
    (hFullSinSqPullback :
      ∀ a a' : E3, G (Ψ a T).1 (Ψ a' T).1 =
        Real.sin θ ^ 2 * S a a')
    (hTimeRadialRadial :
      ∀ u u' : E3,
        G ((Ψ (CartanPullback.radialPart S v u) T).1)
          ((Ψ (CartanPullback.radialPart S v u') T).1) =
          CorrectedRadial.timeRadialScale T *
            S (T⁻¹ • CartanPullback.radialPart S v u)
              (T⁻¹ • CartanPullback.radialPart S v u')) :
    Real.sin θ ^ 2 = 1 := by
  have hrv : CartanPullback.radialPart S v v = v :=
    radialPart_self_of_self_ne_zero hSvv
  have hradial :
      G (Ψ v T).1 (Ψ v T).1 = S v v := by
    calc
      G (Ψ v T).1 (Ψ v T).1 =
          CorrectedRadial.timeRadialScale T * S (T⁻¹ • v) (T⁻¹ • v) := by
            simpa [hrv] using hTimeRadialRadial v v
      _ = CorrectedRadial.timeRadialScale T * ((T⁻¹ * T⁻¹) * S v v) := by
            rw [continuousLinearPairing_inv_smul_inv_smul]
      _ = S v v := by
            rw [← mul_assoc, timeRadialScale_mul_inv_sq T hT]
            simp
  have hpull :
      G (Ψ v T).1 (Ψ v T).1 = Real.sin θ ^ 2 * S v v :=
    hFullSinSqPullback v v
  have hscaled : Real.sin θ ^ 2 * S v v = S v v := by
    rw [← hpull, hradial]
  have hfactor_mul : (Real.sin θ ^ 2 - 1) * S v v = 0 := by
    calc
      (Real.sin θ ^ 2 - 1) * S v v =
          Real.sin θ ^ 2 * S v v - 1 * S v v := by ring
      _ = S v v - S v v := by rw [hscaled]; ring
      _ = 0 := sub_self (S v v)
  have hfactor : Real.sin θ ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hfactor_mul).resolve_right hSvv
  exact sub_eq_zero.mp hfactor

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Source-anchor specialization of
`time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq`.
-/
theorem source_time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T θ : ℝ}
    (hv : v ≠ 0) (hT : T ≠ 0)
    (hFullSinSqPullback :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψ a T).1 (Ψ a' T).1 =
          Real.sin θ ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a')
    (hTimeRadialRadial :
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
                (CartanMap.sourceAnchorChartMetric g x₀) v u')) :
    Real.sin θ ^ 2 = 1 :=
  time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
    (G := CovariantDerivative.chartMetric g.inner x₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v))
    (S := CartanMap.sourceAnchorChartMetric g x₀) (Ψ := Ψ) (v := v)
    (T := T) (θ := θ)
    (CartanPullback.sourceAnchorChartMetric_self_ne_zero
      (g := g) (x₀ := x₀) hv)
    hT hFullSinSqPullback hTimeRadialRadial

/--
Target-anchor specialization of
`time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq`.
-/
theorem target_time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
    (p₀ : RoundSphere3)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T θ : ℝ}
    (hv : v ≠ 0) (hT : T ≠ 0)
    (hFullSinSqPullback :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) v)
            (Ψ a T).1 (Ψ a' T).1 =
          Real.sin θ ^ 2 * CartanMap.targetAnchorChartMetric p₀ a a')
    (hTimeRadialRadial :
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
                (CartanMap.targetAnchorChartMetric p₀) v u')) :
    Real.sin θ ^ 2 = 1 :=
  time_radial_block_and_full_sin_sq_pullback_force_unit_sin_sq
    (G := CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) v))
    (S := CartanMap.targetAnchorChartMetric p₀) (Ψ := Ψ) (v := v)
    (T := T) (θ := θ)
    (CartanPullback.targetAnchorChartMetric_self_ne_zero (p₀ := p₀) hv)
    hT hFullSinSqPullback hTimeRadialRadial

end SinSqInstantiate
end Poincare
