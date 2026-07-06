import Poincare.Global.ConformalCurvature
import Poincare.Global.GeodesicTransport

/-!
# Chart curvature bridge

This module isolates reusable chart-side algebra for the curvature bridge used
by the round-sphere witness.  The proved lemmas move `chartCurvatureOf` through
fixed vector evaluations and rewrite it into the one-form slot convention under
Christoffel symmetry germs.  The remaining model/manifold curvature pushforward
is recorded in the worker report.
-/

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

namespace ChartCurvatureBridge

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/--
Differentiating a continuous-linear-map-valued family commutes with evaluation
at a fixed vector.
-/
theorem fderiv_clm_family_apply
    {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : E → F →L[ℝ] V} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) (v : E) (c : F) :
    (fderiv ℝ Φ x v) c = fderiv ℝ (fun y ↦ Φ y c) x v := by
  have h := (ContinuousLinearMap.apply ℝ V c).hasFDerivAt.comp x
    hΦ.hasFDerivAt
  have hfd :
      fderiv ℝ (fun y ↦ Φ y c) x =
        (ContinuousLinearMap.apply ℝ V c).comp (fderiv ℝ Φ x) :=
    h.fderiv
  rw [hfd]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
`chartCurvatureOf` expanded with the base derivative pushed through the two
fixed vector evaluations.
-/
theorem chartCurvatureOf_eq_fderiv_apply
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : DifferentiableAt ℝ Γ z) (u v w : E) :
    chartCurvatureOf Γ z u v w =
      fderiv ℝ (fun y ↦ Γ y v w) z u
        - fderiv ℝ (fun y ↦ Γ y u w) z v
        + Γ z u (Γ z v w) - Γ z v (Γ z u w) := by
  rw [chartCurvatureOf]
  have hΓv : DifferentiableAt ℝ (fun y ↦ Γ y v) z :=
    hΓ.clm_apply (differentiableAt_const v)
  have hΓu : DifferentiableAt ℝ (fun y ↦ Γ y u) z :=
    hΓ.clm_apply (differentiableAt_const u)
  rw [fderiv_clm_family_apply hΓ u v,
    fderiv_clm_family_apply hΓ v u,
    fderiv_clm_family_apply hΓv u w,
    fderiv_clm_family_apply hΓu v w]

variable [FiniteDimensional ℝ E]

theorem eventually_christoffelOneForm_symm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    {b : Π _ : E, LinearMap.BilinForm ℝ E}
    {hb : ∀ z, (b z).Nondegenerate}
    {z : E}
    (hGd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ G y)
    (hGsymm : ∀ (y p q : E), G y p q = G y q p)
    (u v : E) :
    (fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y) u v)
      =ᶠ[𝓝 z]
    (fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y) v u) := by
  filter_upwards [hGd] with y hGy
  rw [CovariantDerivative.christoffelOneForm_apply,
    CovariantDerivative.christoffelOneForm_apply]
  exact CovariantDerivative.christoffelAt_symm G (b y) (hb y) hGy hGsymm v u

omit [FiniteDimensional ℝ E] in
/--
`chartCurvatureOf` rewritten into the one-form slot convention.  The hypotheses
are exactly the two symmetry germs needed to swap the section and direction
slots in the derivative terms and in the nested Christoffel terms.
-/
theorem chartCurvatureOf_eq_fderiv_apply_swapped_of_eventually_symm
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : DifferentiableAt ℝ Γ z) (u v w : E)
    (hvw : (fun y ↦ Γ y v w) =ᶠ[𝓝 z] fun y ↦ Γ y w v)
    (huw : (fun y ↦ Γ y u w) =ᶠ[𝓝 z] fun y ↦ Γ y w u) :
    chartCurvatureOf Γ z u v w =
      fderiv ℝ (fun y ↦ Γ y w v) z u
        - fderiv ℝ (fun y ↦ Γ y w u) z v
        + Γ z u (Γ z w v) - Γ z v (Γ z w u) := by
  have hder_vw :
      fderiv ℝ (fun y ↦ Γ y v w) z u =
        fderiv ℝ (fun y ↦ Γ y w v) z u := by
    exact congrArg (fun L : E →L[ℝ] E ↦ L u)
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hvw)
  have hder_uw :
      fderiv ℝ (fun y ↦ Γ y u w) z v =
        fderiv ℝ (fun y ↦ Γ y w u) z v := by
    exact congrArg (fun L : E →L[ℝ] E ↦ L v)
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) huw)
  have hΓ_vw : Γ z v w = Γ z w v := hvw.eq_of_nhds
  have hΓ_uw : Γ z u w = Γ z w u := huw.eq_of_nhds
  rw [chartCurvatureOf_eq_fderiv_apply (Γ := Γ) hΓ u v w]
  rw [hder_vw, hder_uw, hΓ_vw, hΓ_uw]

end ChartCurvatureBridge

end Poincare
