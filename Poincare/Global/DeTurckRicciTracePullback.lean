import Poincare.Global.DeTurckGaugePullbackDerivative
import Poincare.Global.RicciTraceConjugacy

/-!
# DeTurck cancellation through the Ricci trace

The chart-level pullback derivative produces the target Ricci bilinear form
evaluated on the gauge differential.  Curvature conjugacy then identifies
that value with the source Ricci trace.  This file composes those two proved
algebraic steps, leaving only the geometric curvature-intertwining law for a
manifold diffeomorphism.
-/

noncomputable section

open scoped Topology

namespace Poincare

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Arbitrary-time inverse-gauge cancellation with the Ricci contraction
transported all the way through curvature conjugacy. -/
theorem hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    (e : E ≃L[ℝ] E)
    (curvSource curvTarget : E → E → (E →ₗ[ℝ] E))
    {t₀ : ℝ}
    (hA : HasDerivAt A (H - adv) t₀)
    (hD : HasDerivAt D (-(DW.comp (D t₀))) t₀)
    (hA₀ : A t₀ = G)
    (hD₀ : D t₀ = e.toContinuousLinearMap)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (hRicciTarget : ∀ u v : E,
      R (e u) (e v) =
        LinearMap.trace ℝ E (curvTarget (e u) (e v)))
    (hcurv : ∀ (u v w : E),
      curvTarget (e u) (e v) (e w) = e (curvSource u v w))
    (u v : E) :
    HasDerivAt (pullbackBilinearApply A D u v)
      ((-2 : ℝ) * LinearMap.trace ℝ E (curvSource u v)) t₀ := by
  have hpull :=
    hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci_comp
      A D G H adv R DW hA hD hA₀ hDeTurck u v
  refine hpull.congr_deriv ?_
  have htrace := ricciTrace_natural_of_curvature_intertwining
    e.toLinearEquiv curvSource curvTarget hcurv u v
  calc
    (-2 : ℝ) * R (D t₀ u) (D t₀ v) =
        (-2 : ℝ) * R (e u) (e v) := by rw [hD₀]; rfl
    _ = (-2 : ℝ) * LinearMap.trace ℝ E (curvTarget (e u) (e v)) := by
      rw [hRicciTarget]
    _ = (-2 : ℝ) * LinearMap.trace ℝ E (curvSource u v) := by
      exact congrArg (fun x : ℝ => (-2 : ℝ) * x) htrace

/-- Derivative-value form of the source-Ricci trace pullback identity. -/
theorem deriv_pullbackBilinearApply_eq_neg_two_source_ricciTrace
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    (e : E ≃L[ℝ] E)
    (curvSource curvTarget : E → E → (E →ₗ[ℝ] E))
    {t₀ : ℝ}
    (hA : HasDerivAt A (H - adv) t₀)
    (hD : HasDerivAt D (-(DW.comp (D t₀))) t₀)
    (hA₀ : A t₀ = G)
    (hD₀ : D t₀ = e.toContinuousLinearMap)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (hRicciTarget : ∀ u v : E,
      R (e u) (e v) =
        LinearMap.trace ℝ E (curvTarget (e u) (e v)))
    (hcurv : ∀ (u v w : E),
      curvTarget (e u) (e v) (e w) = e (curvSource u v w))
    (u v : E) :
    deriv (pullbackBilinearApply A D u v) t₀ =
      (-2 : ℝ) * LinearMap.trace ℝ E (curvSource u v) :=
  (hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace
    A D G H adv R DW e curvSource curvTarget hA hD hA₀ hD₀ hDeTurck
      hRicciTarget hcurv u v).deriv

end Poincare
