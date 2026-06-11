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

open CovariantDerivative Bundle
open scoped Manifold ContDiff

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


/-- The Christoffel corrector as a bilinear map. -/
noncomputable def christoffelLinear (x : F) (b : LinearMap.BilinForm ℝ F)
    (hb : b.Nondegenerate) : F →ₗ[ℝ] F →ₗ[ℝ] F :=
  LinearMap.mk₂ ℝ (fun u v ↦ christoffelAt G x b hb u v)
    (fun u u' v ↦ by
      apply sub_eq_zero.mp
      apply hb.1
      intro w
      simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
      rw [b_christoffelAt, b_christoffelAt, b_christoffelAt]
      simp only [map_add, ContinuousLinearMap.add_apply]
      ring)
    (fun c u v ↦ by
      apply sub_eq_zero.mp
      apply hb.1
      intro w
      simp only [map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [b_christoffelAt, b_christoffelAt]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun u v v' ↦ by
      apply sub_eq_zero.mp
      apply hb.1
      intro w
      simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
      rw [b_christoffelAt, b_christoffelAt, b_christoffelAt]
      simp only [map_add, ContinuousLinearMap.add_apply]
      ring)
    (fun c u v ↦ by
      apply sub_eq_zero.mp
      apply hb.1
      intro w
      simp only [map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [b_christoffelAt, b_christoffelAt]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring)

/-- The Christoffel corrector as a continuous endomorphism-valued one-form
(section value first, direction second), ready for `addOneForm`. -/
noncomputable def christoffelOneForm (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate) (x : F) :
    TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ]
      TangentSpace 𝓘(ℝ, F) x :=
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, F) x) :=
    ‹FiniteDimensional ℝ F›
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (F →ₗ[ℝ] F) ≃ₗ[ℝ] (F →L[ℝ] F)).toLinearMap ∘ₗ
      (christoffelLinear G x (b x) (hb x)).flip)

theorem christoffelOneForm_apply (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate) (x : F)
    (s v : TangentSpace 𝓘(ℝ, F) x) :
    (christoffelOneForm G b hb x : TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x) s v = christoffelAt G x (b x) (hb x) v s :=
  rfl

/--
**The model Levi-Civita connection in Christoffel form**: flat plus the
Christoffel corrector.
-/
noncomputable def modelLeviCivita (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate) :
    CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
  (flatCovariantDerivative ℝ F).addOneForm (fun x ↦ christoffelOneForm G b hb x)

theorem modelLeviCivita_apply (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (σ : Π y : F, TangentSpace 𝓘(ℝ, F) y) (x : F)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    modelLeviCivita G b hb σ x v =
      fderiv ℝ σ x v + christoffelAt G x (b x) (hb x) v (σ x) :=
  rfl


/--
**The Christoffel-form connection is torsion-free**: the corrector's
symmetry cancels in the torsion, leaving the flat torsion, which is the
bracket.
-/
theorem modelLeviCivita_torsionFreeAt
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (hGd : Differentiable ℝ G)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p) (x : F) :
    TorsionFreeAt (modelLeviCivita G b hb) x := by
  intro X Y hX hY
  rw [show (modelLeviCivita G b hb) Y x (X x) =
      fderiv ℝ Y x (X x) + christoffelAt G x (b x) (hb x) (X x) (Y x) from
      rfl,
    show (modelLeviCivita G b hb) X x (Y x) =
      fderiv ℝ X x (Y x) + christoffelAt G x (b x) (hb x) (Y x) (X x) from
      rfl,
    mlieBracket_vectorSpace_eq,
    christoffelAt_symm G (b x) (hb x) (hGd x) hGsymm
      (X x) (Y x)]
  have hlie : VectorField.lieBracket ℝ X Y x =
      fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x) := rfl
  rw [hlie]
  abel


/-- The trilinear product rule: the derivative of the metric pairing of two
fields. -/
theorem fderiv_metric_pairing {x : F} (hGd : DifferentiableAt ℝ G x)
    {Y Z : F → F} (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x) (v : F) :
    fderiv ℝ (fun y ↦ G y (Y y) (Z y)) x v =
      (fderiv ℝ G x v) (Y x) (Z x) + G x (fderiv ℝ Y x v) (Z x)
        + G x (Y x) (fderiv ℝ Z x v) := by
  have hc : DifferentiableAt ℝ (fun y ↦ G y (Y y)) x :=
    hGd.clm_apply hY
  rw [show (fun y ↦ G y (Y y) (Z y)) =
      fun y ↦ ((fun y' ↦ G y' (Y y')) y) (Z y) from rfl,
    fderiv_clm_apply hc hZ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.flip_apply]
  rw [show (fun y ↦ G y (Y y)) = fun y ↦ (G y) (Y y) from rfl,
    fderiv_clm_apply hGd hY]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.flip_apply]
  ring

/--
**The Christoffel-form connection is metric-compatible**: the derivative of
the pairing satisfies the Riemannian product rule, with the corrector terms
supplying exactly the metric derivative by the defining property and the
derivative symmetry.
-/
theorem modelLeviCivita_metricCompatibleAt
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (hGd : Differentiable ℝ G)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p)
    (hbg : ∀ (x : F) (v w : F), b x v w = G x v w) (x : F) :
    MetricCompatibleAt G (modelLeviCivita G b hb) x := by
  intro Y Z hY hZ v
  have hY' := mdiffAt_vectorSpace_iff_differentiableAt.mp hY
  have hZ' := mdiffAt_vectorSpace_iff_differentiableAt.mp hZ
  have h1 : G x (christoffelAt G x (b x) (hb x) v (Y x)) (Z x) =
      (1 / 2 : ℝ) * ((fderiv ℝ G x v) (Y x) (Z x)
        + (fderiv ℝ G x (Y x)) v (Z x) - (fderiv ℝ G x (Z x)) v (Y x)) := by
    rw [← hbg]
    exact b_christoffelAt G x (b x) (hb x) v (Y x) (Z x)
  have h2 : G x (Y x) (christoffelAt G x (b x) (hb x) v (Z x)) =
      (1 / 2 : ℝ) * ((fderiv ℝ G x v) (Z x) (Y x)
        + (fderiv ℝ G x (Z x)) v (Y x) - (fderiv ℝ G x (Y x)) v (Z x)) := by
    rw [hGsymm x, ← hbg]
    exact b_christoffelAt G x (b x) (hb x) v (Z x) (Y x)
  have hsym := fderiv_metric_symm G (hGd x) hGsymm v (Y x) (Z x)
  have key : fderiv ℝ (fun y ↦ G y (Y y) (Z y)) x v =
      G x ((modelLeviCivita G b hb) Y x v) (Z x)
        + G x (Y x) ((modelLeviCivita G b hb) Z x v) := by
    rw [fderiv_metric_pairing G (hGd x) hY' hZ' v,
      show (modelLeviCivita G b hb) Y x v =
        fderiv ℝ Y x v + christoffelAt G x (b x) (hb x) v (Y x) from rfl,
      show (modelLeviCivita G b hb) Z x v =
        fderiv ℝ Z x v + christoffelAt G x (b x) (hb x) v (Z x) from rfl]
    simp only [map_add, ContinuousLinearMap.add_apply]
    rw [h1, h2]
    linarith [hsym]
  refine Eq.trans ?_ key
  simp only [extDerivFun, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
  rfl

end CovariantDerivative
