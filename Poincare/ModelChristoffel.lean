/-
Christoffel symbols on the model space.

For a metric `G` on a normed space, the Christoffel corrector at `x` is the
bilinear map `Γₓ` determined by
`2 G x (Γₓ(u,v), w) = (DG·u)(v,w) + (DG·v)(u,w) − (DG·w)(u,v)`.
The Levi-Civita connection of `G` is `flat + Γ`; since `Γ` is built from one
derivative of `G`, smoothness of the connection in the base point reduces
to smoothness of `G` — the gateway to the PDE stratum.

This module defines `Γ` via the metric dual and proves its defining
property and symmetry.
-/

import Poincare.KoszulExistence

noncomputable section

open CovariantDerivative

namespace CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable (G : F → F →L[ℝ] F →L[ℝ] ℝ)

/-- The Koszul corrector functional of the metric `G` at `x` in directions
`u, v`, as a linear functional in the test vector. -/
noncomputable def christoffelFunctional (x u v : F) :
    F →ₗ[ℝ] ℝ where
  toFun w := (1 / 2 : ℝ) *
    ((fderiv ℝ G x u) v w + (fderiv ℝ G x v) u w - (fderiv ℝ G x w) u v)
  map_add' w w' := by
    simp only [map_add, ContinuousLinearMap.add_apply]
    ring
  map_smul' c w := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- The Christoffel corrector of `G` at `x`: the metric dual of the Koszul
corrector functional. -/
noncomputable def christoffelAt (x : F)
    (b : LinearMap.BilinForm ℝ F) (hb : b.Nondegenerate) (u v : F) : F :=
  (LinearMap.BilinForm.toDual b hb).symm (christoffelFunctional G x u v)

/-- **Defining property of the Christoffel corrector.** -/
theorem b_christoffelAt (x : F) (b : LinearMap.BilinForm ℝ F)
    (hb : b.Nondegenerate) (u v w : F) :
    b (christoffelAt G x b hb u v) w = (1 / 2 : ℝ) *
      ((fderiv ℝ G x u) v w + (fderiv ℝ G x v) u w
        - (fderiv ℝ G x w) u v) := by
  unfold christoffelAt
  have h := LinearEquiv.apply_symm_apply
    (LinearMap.BilinForm.toDual b hb) (christoffelFunctional G x u v)
  have h2 := congrArg (fun ψ ↦ ψ w) h
  simpa [LinearMap.BilinForm.toDual_def, christoffelFunctional] using h2

/-- The derivative of a symmetric-valued metric is symmetric-valued. -/
theorem fderiv_metric_symm {x : F} (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p) (u p q : F) :
    (fderiv ℝ G x u) p q = (fderiv ℝ G x u) q p := by
  set L : (F →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ q).comp
      (ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) p)
    - (ContinuousLinearMap.apply ℝ ℝ p).comp
      (ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) q) with hL
  have hzero : (fun y ↦ L (G y)) = fun _ ↦ (0 : ℝ) := by
    funext y
    simp [hL, hGsymm y p q]
  have hcomp : fderiv ℝ (fun y ↦ L (G y)) x = L.comp (fderiv ℝ G x) := by
    rw [show (fun y ↦ L (G y)) = L ∘ G from rfl,
      fderiv_comp x L.differentiableAt hGd, L.fderiv]
  rw [hzero] at hcomp
  have h0 : (0 : F →L[ℝ] ℝ) = L.comp (fderiv ℝ G x) := by
    rw [← hcomp]
    simp
  have := congrArg (fun T ↦ T u) h0
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
    hL, ContinuousLinearMap.sub_apply, ContinuousLinearMap.apply_apply] at this
  linarith

/-- The Christoffel corrector is symmetric in its two directions. -/
theorem christoffelAt_symm {x : F} (b : LinearMap.BilinForm ℝ F)
    (hb : b.Nondegenerate) (hGd : DifferentiableAt ℝ G x)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p) (u v : F) :
    christoffelAt G x b hb u v = christoffelAt G x b hb v u := by
  apply sub_eq_zero.mp
  apply hb.1
  intro w
  simp only [map_sub, LinearMap.sub_apply]
  rw [b_christoffelAt, b_christoffelAt,
    fderiv_metric_symm G hGd hGsymm w u v]
  ring

end CovariantDerivative
