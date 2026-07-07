import Poincare.Global.CartanIsometry
import Poincare.Global.ExponentialRayLaw

/-!
# Cartan pullback strict partial

This module isolates the first non-vacuous algebraic piece of the Cartan
pullback identity: radial/transverse decomposition in the anchor chart metric.

For a positive-definite anchor chart metric `B` and a nonzero radial vector
`v`, any chart vector `u` splits as

`u = radialPart B v u + transversePart B v u`,

where the transverse part is `B`-orthogonal to `v`.  The same algebra gives the
metric decomposition into radial and transverse blocks.  The final lemmas show
that a `CartanMap.TangentAlignment` transports the coefficient and both parts
from the source anchor metric to the round-sphere anchor metric.  These are the
Gram-algebra ingredients needed before the still-missing nonzero-point
exponential differential and chain-rule assembly.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanPullback

local notation "E" => ClosedSmoothModel 3

/-- Coefficient of the projection of `u` onto the line spanned by `v` for `B`. -/
def radialCoeff (B : E →L[ℝ] E →L[ℝ] ℝ) (v u : E) : ℝ :=
  B u v / B v v

/-- The radial component of `u` along `v` for the bilinear form `B`. -/
def radialPart (B : E →L[ℝ] E →L[ℝ] ℝ) (v u : E) : E :=
  radialCoeff B v u • v

/-- The transverse component of `u` for the bilinear form `B` and radial vector `v`. -/
def transversePart (B : E →L[ℝ] E →L[ℝ] ℝ) (v u : E) : E :=
  u - radialPart B v u

@[simp]
theorem radialPart_add_transversePart
    (B : E →L[ℝ] E →L[ℝ] ℝ) (v u : E) :
    radialPart B v u + transversePart B v u = u := by
  simp [transversePart]

@[simp]
theorem transversePart_add_radialPart
    (B : E →L[ℝ] E →L[ℝ] ℝ) (v u : E) :
    transversePart B v u + radialPart B v u = u := by
  rw [add_comm, radialPart_add_transversePart]

theorem radialPart_pair_self_right
    {B : E →L[ℝ] E →L[ℝ] ℝ} {v u : E}
    (hvv : B v v ≠ 0) :
    B (radialPart B v u) v = B u v := by
  simp [radialPart, radialCoeff, hvv]

theorem transversePart_pair_self_right
    {B : E →L[ℝ] E →L[ℝ] ℝ} {v u : E}
    (hvv : B v v ≠ 0) :
    B (transversePart B v u) v = 0 := by
  simp [transversePart, radialPart_pair_self_right (B := B) (v := v) (u := u) hvv]

theorem transversePart_pair_self_left
    {B : E →L[ℝ] E →L[ℝ] ℝ} {v u : E}
    (hsymm : ∀ x y : E, B x y = B y x)
    (hvv : B v v ≠ 0) :
    B v (transversePart B v u) = 0 := by
  rw [hsymm, transversePart_pair_self_right (B := B) (v := v) (u := u) hvv]

theorem radialPart_transversePart_pair
    {B : E →L[ℝ] E →L[ℝ] ℝ} {v u u' : E}
    (hsymm : ∀ x y : E, B x y = B y x)
    (hvv : B v v ≠ 0) :
    B (radialPart B v u) (transversePart B v u') = 0 := by
  simp [radialPart, transversePart_pair_self_left (B := B) (v := v) (u := u') hsymm hvv]

theorem transversePart_radialPart_pair
    {B : E →L[ℝ] E →L[ℝ] ℝ} {v u u' : E}
    (hvv : B v v ≠ 0) :
    B (transversePart B v u) (radialPart B v u') = 0 := by
  simp [radialPart, transversePart_pair_self_right (B := B) (v := v) (u := u) hvv]

/--
The Gram decomposition of the metric into its radial and transverse blocks.
The two mixed blocks vanish by orthogonality to `v`.
-/
theorem pair_eq_radial_add_transverse
    {B : E →L[ℝ] E →L[ℝ] ℝ} {v u u' : E}
    (hsymm : ∀ x y : E, B x y = B y x)
    (hvv : B v v ≠ 0) :
    B u u' =
      B (radialPart B v u) (radialPart B v u') +
        B (transversePart B v u) (transversePart B v u') := by
  let r : E := radialPart B v u
  let t : E := transversePart B v u
  let r' : E := radialPart B v u'
  let t' : E := transversePart B v u'
  have hu : u = r + t := by
    simp [r, t]
  have hu' : u' = r' + t' := by
    simp [r', t']
  have hrt' : B r t' = 0 := by
    simpa [r, t'] using
      radialPart_transversePart_pair (B := B) (v := v) (u := u) (u' := u') hsymm hvv
  have htr' : B t r' = 0 := by
    simpa [t, r'] using
      transversePart_radialPart_pair (B := B) (v := v) (u := u) (u' := u') hvv
  calc
    B u u' = B (r + t) (r' + t') := by rw [hu, hu']
    _ = B r r' + B t t' := by
      simp only [map_add, ContinuousLinearMap.add_apply, hrt', htr', zero_add, add_zero]
    _ = B (radialPart B v u) (radialPart B v u') +
        B (transversePart B v u) (transversePart B v u') := rfl

variable {M : Type*}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

theorem sourceAnchorChartMetric_self_ne_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {v : E} (hv : v ≠ 0) :
    CartanMap.sourceAnchorChartMetric g x₀ v v ≠ 0 :=
  ne_of_gt (CartanMap.sourceAnchorChartMetric_pos g x₀ hv)

theorem targetAnchorChartMetric_self_ne_zero
    (p₀ : RoundSphere3) {v : E} (hv : v ≠ 0) :
    CartanMap.targetAnchorChartMetric p₀ v v ≠ 0 :=
  ne_of_gt (CartanMap.targetAnchorChartMetric_pos p₀ hv)

/-- Source-anchor radial/transverse Gram decomposition. -/
theorem sourceAnchorChartMetric_pair_eq_radial_add_transverse
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {v : E} (hv : v ≠ 0)
    (u u' : E) :
    CartanMap.sourceAnchorChartMetric g x₀ u u' =
      CartanMap.sourceAnchorChartMetric g x₀
          (radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u)
          (radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u') +
        CartanMap.sourceAnchorChartMetric g x₀
          (transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u)
          (transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u') := by
  exact
    pair_eq_radial_add_transverse
      (B := CartanMap.sourceAnchorChartMetric g x₀) (v := v) (u := u) (u' := u')
      (CartanMap.sourceAnchorChartMetric_symm g x₀)
      (sourceAnchorChartMetric_self_ne_zero (g := g) (x₀ := x₀) hv)

/-- Target-anchor radial/transverse Gram decomposition. -/
theorem targetAnchorChartMetric_pair_eq_radial_add_transverse
    (p₀ : RoundSphere3) {v : E} (hv : v ≠ 0) (u u' : E) :
    CartanMap.targetAnchorChartMetric p₀ u u' =
      CartanMap.targetAnchorChartMetric p₀
          (radialPart (CartanMap.targetAnchorChartMetric p₀) v u)
          (radialPart (CartanMap.targetAnchorChartMetric p₀) v u') +
        CartanMap.targetAnchorChartMetric p₀
          (transversePart (CartanMap.targetAnchorChartMetric p₀) v u)
          (transversePart (CartanMap.targetAnchorChartMetric p₀) v u') := by
  exact
    pair_eq_radial_add_transverse
      (B := CartanMap.targetAnchorChartMetric p₀) (v := v) (u := u) (u' := u')
      (CartanMap.targetAnchorChartMetric_symm p₀)
      (targetAnchorChartMetric_self_ne_zero (p₀ := p₀) hv)

/--
A Cartan tangent alignment preserves the scalar radial projection coefficient.
This is the algebraic reason the source and target decompositions carry the
same radial/transverse factors at the anchors.
-/
theorem tangentAlignment_radialCoeff_map
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v u : E) :
    radialCoeff (CartanMap.targetAnchorChartMetric p₀) (L v) (L u) =
      radialCoeff (CartanMap.sourceAnchorChartMetric g x₀) v u := by
  simp [radialCoeff, CartanMap.TangentAlignment.map_app]

/-- A Cartan tangent alignment transports source radial parts to target radial parts. -/
theorem tangentAlignment_radialPart_map
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v u : E) :
    radialPart (CartanMap.targetAnchorChartMetric p₀) (L v) (L u) =
      L (radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u) := by
  simp [radialPart, tangentAlignment_radialCoeff_map]

/-- A Cartan tangent alignment transports source transverse parts to target transverse parts. -/
theorem tangentAlignment_transversePart_map
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v u : E) :
    transversePart (CartanMap.targetAnchorChartMetric p₀) (L v) (L u) =
      L (transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u) := by
  simp [transversePart, tangentAlignment_radialPart_map]

end CartanPullback
end Poincare
