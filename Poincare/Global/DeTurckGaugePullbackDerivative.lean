import Poincare.Global.DeTurckLocalFrameRegularity
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Time derivative of a gauge-pulled bilinear form

This file isolates the calculus identity at the heart of the DeTurck gauge
pullback.  At a fixed source point and in fixed chart coordinates, a pulled
metric has the form

    A(t) (D(t) u) (D(t) v),

where A(t) is the metric evaluated along the moving base point and D(t) is
the derivative of the gauge map.  Differentiating gives the metric term and
the two moving-slot terms.  For an inverse DeTurck gauge, the base-advection
and slot terms cancel the Lie derivative in the Ricci--DeTurck equation.

The results below are actual derivative identities.  They do not rely on an assumed
global manifold flow or hide the pullback step behind another proposition.
The remaining global work is to construct the gauge flow and identify these
chart-level derivatives with the geometric pullback and Ricci tensor.
-/

noncomputable section

open scoped Topology

namespace Poincare

section PullbackCalculus

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar value of a time-dependent bilinear form pulled through a
time-dependent linear map. -/
def pullbackBilinearApply
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (u v : E) (t : ℝ) : ℝ :=
  A t (D t u) (D t v)

/--
Product and chain rule for a pulled-back bilinear form at a fixed source
point.
-/
theorem hasDerivAt_pullbackBilinearApply
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    {t₀ : ℝ} {A' : E →L[ℝ] E →L[ℝ] ℝ} {D' : E →L[ℝ] E}
    (hA : HasDerivAt A A' t₀) (hD : HasDerivAt D D' t₀)
    (u v : E) :
    HasDerivAt (pullbackBilinearApply A D u v)
      (A' (D t₀ u) (D t₀ v) +
        A t₀ (D' u) (D t₀ v) +
        A t₀ (D t₀ u) (D' v)) t₀ := by
  have hDu : HasDerivAt (fun t : ℝ ↦ D t u) (D' u) t₀ :=
    by simpa using hD.clm_apply (hasDerivAt_const t₀ u)
  have hDv : HasDerivAt (fun t : ℝ ↦ D t v) (D' v) t₀ :=
    by simpa using hD.clm_apply (hasDerivAt_const t₀ v)
  have hAu : HasDerivAt (fun t : ℝ ↦ A t (D t u))
      (A' (D t₀ u) + A t₀ (D' u)) t₀ :=
    hA.clm_apply hDu
  have h := hAu.clm_apply hDv
  simpa [pullbackBilinearApply, ContinuousLinearMap.add_apply, add_assoc] using h

/-- At an identity gauge time, the pulled bilinear form has the original
bilinear value. -/
theorem pullbackBilinearApply_at_identity
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (t₀ : ℝ)
    (hA₀ : A t₀ = G)
    (hD₀ : D t₀ = ContinuousLinearMap.id ℝ E)
    (u v : E) :
    pullbackBilinearApply A D u v t₀ = G u v := by
  simp [pullbackBilinearApply, hA₀, hD₀]

/--
DeTurck cancellation at an arbitrary time of the inverse gauge flow.

Here `D t₀` is the differential of the inverse gauge at the source point.
The equation `D' = -(DW ∘ D)` is the differentiated inverse-flow equation.
No identity-gauge assumption is needed: the result is the pullback of the
Ricci bilinear form through `D t₀`.
-/
theorem hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci_comp
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    {t₀ : ℝ}
    (hA : HasDerivAt A (H - adv) t₀)
    (hD : HasDerivAt D (-(DW.comp (D t₀))) t₀)
    (hA₀ : A t₀ = G)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (u v : E) :
    HasDerivAt (pullbackBilinearApply A D u v)
      ((-2 : ℝ) * R (D t₀ u) (D t₀ v)) t₀ := by
  have h := hasDerivAt_pullbackBilinearApply A D hA hD u v
  refine h.congr_deriv ?_
  rw [hA₀]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, map_neg]
  rw [hDeTurck]
  ring

/-- Derivative-value form of arbitrary-time inverse-gauge cancellation. -/
theorem deriv_pullbackBilinearApply_eq_neg_two_ricci_comp
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    {t₀ : ℝ}
    (hA : HasDerivAt A (H - adv) t₀)
    (hD : HasDerivAt D (-(DW.comp (D t₀))) t₀)
    (hA₀ : A t₀ = G)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (u v : E) :
    deriv (pullbackBilinearApply A D u v) t₀ =
      (-2 : ℝ) * R (D t₀ u) (D t₀ v) :=
  (hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci_comp
    A D G H adv R DW hA hD hA₀ hDeTurck u v).deriv

/--
Initial-time DeTurck cancellation for an inverse gauge.

H is the fixed-base metric time derivative, adv is the derivative caused by
moving the base point along the DeTurck vector field, DW is the spatial
derivative of that field, and R is the Ricci bilinear form.  The displayed
equation is the chart spelling of H = -2 Ric + L_W G.

If the inverse gauge starts at the identity, moves the base point with
derivative -W, and has differential derivative -DW, then the derivative of
the pulled metric is exactly -2 Ric.
-/
theorem hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    {t₀ : ℝ}
    (hA : HasDerivAt A (H - adv) t₀)
    (hD : HasDerivAt D (-DW) t₀)
    (hA₀ : A t₀ = G)
    (hD₀ : D t₀ = ContinuousLinearMap.id ℝ E)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (u v : E) :
    HasDerivAt (pullbackBilinearApply A D u v)
      ((-2 : ℝ) * R u v) t₀ := by
  have h := hasDerivAt_pullbackBilinearApply A D hA hD u v
  refine h.congr_deriv ?_
  rw [hA₀, hD₀]
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, map_neg]
  rw [hDeTurck]
  ring

/-- Derivative-value form of the inverse-gauge cancellation theorem. -/
theorem deriv_pullbackBilinearApply_eq_neg_two_ricci
    (A : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (D : ℝ → E →L[ℝ] E)
    (G H adv R : E →L[ℝ] E →L[ℝ] ℝ) (DW : E →L[ℝ] E)
    {t₀ : ℝ}
    (hA : HasDerivAt A (H - adv) t₀)
    (hD : HasDerivAt D (-DW) t₀)
    (hA₀ : A t₀ = G)
    (hD₀ : D t₀ = ContinuousLinearMap.id ℝ E)
    (hDeTurck : ∀ u v : E,
      H u v =
        (-2 : ℝ) * R u v + adv u v +
          G (DW u) v + G u (DW v))
    (u v : E) :
    deriv (pullbackBilinearApply A D u v) t₀ =
      (-2 : ℝ) * R u v :=
  (hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci
    A D G H adv R DW hA hD hA₀ hD₀ hDeTurck u v).deriv

end PullbackCalculus

end Poincare
