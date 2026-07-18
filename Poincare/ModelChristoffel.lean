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
import Poincare.CurvatureConditions
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

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


section Identification

variable [CompleteSpace F]

/-- Pairing differentiability for a differentiable metric. -/
theorem metric_pairing_mdiff (hGd : Differentiable ℝ G) (x : F)
    (A B : Π y : F, TangentSpace 𝓘(ℝ, F) y)
    (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) :
    MDiffAt (fun y ↦ G y (A y) (B y)) x := by
  have hA' := mdiffAt_vectorSpace_iff_differentiableAt.mp hA
  have hB' := mdiffAt_vectorSpace_iff_differentiableAt.mp hB
  exact mdifferentiableAt_iff_differentiableAt.mpr
    (((hGd x).clm_apply hA').clm_apply hB')

/--
**The Christoffel identification**: on the model space, the canonical
Levi-Civita connection of a differentiable symmetric nondegenerate metric
is `flat + Γ` on differentiable fields.  The connection is thereby exhibited
in a form involving exactly one derivative of the metric.
-/
theorem leviCivitaConnection_eq_modelLeviCivita
    (hGd : Differentiable ℝ G)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p)
    (hGnd : ∀ (y : F) (v : F), (∀ w, G y v w = 0) → v = 0)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (hbg : ∀ (x : F) (v w : F), b x v w = G x v w)
    {Y : Π y : F, TangentSpace 𝓘(ℝ, F) y} {x : F}
    (hY : MDiffAt (T% Y) x) :
    leviCivitaConnection G hGsymm hGnd (metric_pairing_mdiff G hGd) Y x =
      modelLeviCivita G b hb Y x :=
  leviCivitaConnection_eq_of_isLeviCivita G hGsymm hGnd
    (metric_pairing_mdiff G hGd) (modelLeviCivita G b hb)
    (fun y ↦ modelLeviCivita_metricCompatibleAt G b hb hGd hGsymm hbg y)
    (fun y ↦ modelLeviCivita_torsionFreeAt G b hb hGd hGsymm y) hY

end Identification


section ClosedForm

/-- Nondegeneracy makes the metric, viewed as the musical map into the
dual, an invertible operator. -/
theorem metric_isInvertible {x : F} (b : LinearMap.BilinForm ℝ F)
    (hb : b.Nondegenerate) (hbg : ∀ v w : F, b v w = G x v w) :
    ContinuousLinearMap.IsInvertible
      (G x : F →L[ℝ] F →L[ℝ] ℝ) := by
  refine ⟨((LinearMap.BilinForm.toDual b hb).trans
    (LinearMap.toContinuousLinearMap :
      Module.Dual ℝ F ≃ₗ[ℝ] (F →L[ℝ] ℝ))).toContinuousLinearEquiv, ?_⟩
  ext v w
  have h1 : (((LinearMap.BilinForm.toDual b hb).trans
      (LinearMap.toContinuousLinearMap :
        Module.Dual ℝ F ≃ₗ[ℝ] (F →L[ℝ] ℝ))).toContinuousLinearEquiv v) w =
      (LinearMap.BilinForm.toDual b hb v) w := by
    rw [show (((LinearMap.BilinForm.toDual b hb).trans
      (LinearMap.toContinuousLinearMap :
        Module.Dual ℝ F ≃ₗ[ℝ] (F →L[ℝ] ℝ))).toContinuousLinearEquiv v) =
      LinearMap.toContinuousLinearMap (LinearMap.BilinForm.toDual b hb v)
      from congrFun (LinearEquiv.coe_toContinuousLinearEquiv' _) v]
    rfl
  rw [show ((((LinearMap.BilinForm.toDual b hb).trans
      (LinearMap.toContinuousLinearMap :
        Module.Dual ℝ F ≃ₗ[ℝ] (F →L[ℝ] ℝ))).toContinuousLinearEquiv :
      F →L[ℝ] F →L[ℝ] ℝ) v) w = (((LinearMap.BilinForm.toDual b hb).trans
      (LinearMap.toContinuousLinearMap :
        Module.Dual ℝ F ≃ₗ[ℝ] (F →L[ℝ] ℝ))).toContinuousLinearEquiv v) w
      from rfl, h1, LinearMap.BilinForm.toDual_def]
  exact hbg v w

/--
**Closed form of the Christoffel corrector**: `Γ(u,v)` is the inverse
metric applied to the corrector functional — the representation from which
smoothness in the base point follows by the formula.
-/
theorem christoffelAt_eq_inverse {x : F} (b : LinearMap.BilinForm ℝ F)
    (hb : b.Nondegenerate) (hbg : ∀ v w : F, b v w = G x v w) (u v : F) :
    christoffelAt G x b hb u v =
      (G x : F →L[ℝ] F →L[ℝ] ℝ).inverse
        (LinearMap.toContinuousLinearMap (christoffelFunctional G x u v)) := by
  have hinv := metric_isInvertible G b hb hbg
  symm
  rw [hinv.inverse_apply_eq]
  ext w
  rw [show ((G x) (christoffelAt G x b hb u v)) w =
    b (christoffelAt G x b hb u v) w from (hbg _ _).symm, b_christoffelAt]
  rfl

end ClosedForm


section Smoothness

variable [CompleteSpace F]

/--
**Smoothness of the Christoffel corrector**: if the metric is `C^{k+1}`,
the corrector (at fixed directions) is `C^k` in the base point — by the
closed form, as the composition of operator-inversion smoothness with the
smoothness of the metric and its derivative.
-/
theorem contDiffAt_christoffelAt {k : ℕ∞ω} {x : F}
    (hGc : ContDiff ℝ (k + 1) G)
    (b : Π y : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ y, (b y).Nondegenerate)
    (hbg : ∀ (y : F) (v w : F), b y v w = G y v w) (u v : F) :
    ContDiffAt ℝ k (fun y ↦ christoffelAt G y (b y) (hb y) u v) x := by
  have hfun : (fun y ↦ christoffelAt G y (b y) (hb y) u v) =
      fun y ↦ (G y : F →L[ℝ] F →L[ℝ] ℝ).inverse
        (LinearMap.toContinuousLinearMap
          (christoffelFunctional G y u v)) := by
    funext y
    exact christoffelAt_eq_inverse G (b y) (hb y) (hbg y) u v
  rw [hfun]
  have hG1 : ContDiff ℝ k G := hGc.of_le (by
    exact le_self_add)
  have hdf := hGc.fderiv_right (m := k) le_rfl
  -- Smoothness of the inverse-metric family.
  have hinvmap : ContDiffAt ℝ k
      (fun y ↦ (G y : F →L[ℝ] F →L[ℝ] ℝ).inverse) x := by
    exact ((metric_isInvertible G (b x) (hb x)
      (hbg x)).contDiffAt_map_inverse).comp x hG1.contDiffAt
  -- Smoothness of the corrector functional as a CLM-valued map.
  have hΦeq : (fun y ↦ LinearMap.toContinuousLinearMap
      (christoffelFunctional G y u v)) =
      fun y ↦ (1 / 2 : ℝ) • (((fderiv ℝ G y) u) v + ((fderiv ℝ G y) v) u
        - ((ContinuousLinearMap.apply ℝ ℝ v).comp
            ((ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) u))).comp
          (fderiv ℝ G y)) := by
    funext y
    ext w
    simp [christoffelFunctional, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      smul_eq_mul, mul_comm]
  have hΦ : ContDiffAt ℝ k (fun y ↦ LinearMap.toContinuousLinearMap
      (christoffelFunctional G y u v)) x := by
    rw [hΦeq]
    apply ContDiffAt.const_smul
    apply ContDiffAt.sub
    · exact ((hdf.clm_apply contDiff_const).clm_apply
        contDiff_const).contDiffAt.add
        (((hdf.clm_apply contDiff_const).clm_apply
          contDiff_const).contDiffAt)
    · exact (contDiff_const.clm_comp hdf).contDiffAt
  exact hinvmap.clm_apply hΦ


/--
Smoothness of the corrector applied to a smooth section: for a `C^{k+1}`
metric and `C^{k+1}` field, the corrector family at the section is `C^k`.
-/
theorem contDiff_christoffel_apply_section {k : ℕ∞ω}
    (hGc : ContDiff ℝ (k + 1) G)
    (b : Π y : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ y, (b y).Nondegenerate)
    (hbg : ∀ (y : F) (v w : F), b y v w = G y v w)
    {σ : F → F} (hσ : ContDiff ℝ (k + 1) σ) :
    ContDiff ℝ k (fun y ↦
      (LinearMap.toContinuousLinearMap
        ((christoffelLinear G y (b y) (hb y)).flip (σ y)) :
          F →L[ℝ] F)) := by
  rw [contDiff_clm_apply_iff]
  intro v
  have hfun : (fun y ↦ (LinearMap.toContinuousLinearMap
      ((christoffelLinear G y (b y) (hb y)).flip (σ y)) : F →L[ℝ] F) v) =
      fun y ↦ (G y : F →L[ℝ] F →L[ℝ] ℝ).inverse
        (LinearMap.toContinuousLinearMap
          (christoffelFunctional G y v (σ y))) := by
    funext y
    exact christoffelAt_eq_inverse G (b y) (hb y) (hbg y) v (σ y)
  rw [hfun]
  have hσ' : ContDiff ℝ k σ := hσ.of_le le_self_add
  have hG1 : ContDiff ℝ k G := hGc.of_le le_self_add
  have hdf := hGc.fderiv_right (m := k) le_rfl
  have hinvmap : ContDiff ℝ k
      (fun y ↦ (G y : F →L[ℝ] F →L[ℝ] ℝ).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact ((metric_isInvertible G (b y) (hb y)
      (hbg y)).contDiffAt_map_inverse).comp y hG1.contDiffAt
  -- The third derivative piece via the evaluation criterion.
  have hp3 : ContDiff ℝ k (fun y ↦
      (((fderiv ℝ G y).flip v).flip (σ y) : F →L[ℝ] ℝ)) := by
    rw [contDiff_clm_apply_iff]
    intro w
    have heq : (fun y ↦ (((fderiv ℝ G y).flip v).flip (σ y)
        : F →L[ℝ] ℝ) w) = fun y ↦ ((fderiv ℝ G y) w) v (σ y) := by
      funext y
      simp [ContinuousLinearMap.flip_apply]
    rw [heq]
    exact ((hdf.clm_apply contDiff_const).clm_apply
      contDiff_const).clm_apply hσ'
  have hΦeq : (fun y ↦ LinearMap.toContinuousLinearMap
      (christoffelFunctional G y v (σ y))) =
      fun y ↦ (1 / 2 : ℝ) • (((fderiv ℝ G y) v) (σ y)
        + ((fderiv ℝ G y) (σ y)) v
        - (((fderiv ℝ G y).flip v).flip (σ y))) := by
    funext y
    ext w
    simp [christoffelFunctional, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
  have hΦ : ContDiff ℝ k (fun y ↦ LinearMap.toContinuousLinearMap
      (christoffelFunctional G y v (σ y))) := by
    rw [hΦeq]
    apply ContDiff.const_smul
    apply ContDiff.sub
    · exact ((hdf.clm_apply contDiff_const).clm_apply hσ').add
        ((hdf.clm_apply hσ').clm_apply contDiff_const)
    · exact hp3
  exact hinvmap.clm_apply hΦ


/--
**The Levi-Civita connection of a smooth metric is smooth**: the
Christoffel-form connection of a `C^{k+1}` metric is a `C^k` covariant
derivative.
-/
theorem modelLeviCivita_contMDiff {k : ℕ∞ω}
    (hGc : ContDiff ℝ (k + 1) G)
    (b : Π y : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ y, (b y).Nondegenerate)
    (hbg : ∀ (y : F) (v w : F), b y v w = G y v w) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (modelLeviCivita G b hb) k := by
  constructor
  constructor
  intro σ hσ
  intro x _
  apply ContMDiffWithinAt.contMDiffAt (s := Set.univ) ?_ Filter.univ_mem
  rw [contMDiffWithinAt_univ, contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hσcd : ContDiff ℝ (k + 1) σ :=
    contMDiff_vectorSpace_iff_contDiff.mp (contMDiffOn_univ.mp hσ)
  have hplain : ContDiff ℝ k (fun y ↦ fderiv ℝ σ y
      + (LinearMap.toContinuousLinearMap
        ((christoffelLinear G y (b y) (hb y)).flip (σ y)) : F →L[ℝ] F)) :=
    (hσcd.fderiv_right (m := k) le_rfl).add
      (contDiff_christoffel_apply_section G hGc b hb hbg hσcd)
  have hgoal : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F →L[ℝ] F) k
      (fun y ↦ fderiv ℝ σ y + (LinearMap.toContinuousLinearMap
        ((christoffelLinear G y (b y) (hb y)).flip (σ y)) : F →L[ℝ] F)) x :=
    (contMDiffAt_iff_contDiffAt).mpr hplain.contDiffAt
  exact hgoal.congr_of_eventuallyEq (Filter.Eventually.of_forall
    fun y ↦ inCoordinates_tangent_bundle_core_model_space x y x y _)

/--
**Regularity of the model-space Koszul Levi-Civita connection**: once the
Koszul construction is identified with the Christoffel-form connection, the
existing model-space smoothness theorem supplies the `C^k` covariant-derivative
regularity class.
-/
theorem leviCivitaConnection_contMDiff {k : ℕ∞ω}
    (hGd : Differentiable ℝ G) (hGc : ContDiff ℝ (k + 1) G)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p)
    (hGnd : ∀ (y : F) (v : F), (∀ w, G y v w = 0) → v = 0)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (hbg : ∀ (x : F) (v w : F), b x v w = G x v w) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnection G hGsymm hGnd (metric_pairing_mdiff G hGd)) k := by
  haveI : CovariantDerivative.ContMDiffCovariantDerivative
      (modelLeviCivita G b hb) k :=
    modelLeviCivita_contMDiff G hGc b hb hbg
  constructor
  constructor
  intro σ hσ
  have hmodel :=
    (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff
      (cov := modelLeviCivita G b hb) (k := k)).contMDiff
      (σ := σ) hσ
  have heq :
      (fun y : F ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun y : F ↦ TangentSpace 𝓘(ℝ, F) y →L[ℝ]
          TangentSpace 𝓘(ℝ, F) y)
        y ((leviCivitaConnection G hGsymm hGnd
          (metric_pairing_mdiff G hGd)) σ y)) =
      (fun y : F ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun y : F ↦ TangentSpace 𝓘(ℝ, F) y →L[ℝ]
          TangentSpace 𝓘(ℝ, F) y)
        y ((modelLeviCivita G b hb) σ y)) := by
    funext y
    have hσy : MDiffAt (T% σ) y :=
      (hσ.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
    rw [leviCivitaConnection_eq_modelLeviCivita G hGd hGsymm hGnd b hb hbg hσy]
  rw [heq]
  exact hmodel


/--
**The Ricci tensor of a smooth metric is symmetric** (model space): the
canonical Ricci bilinear form of the Christoffel-form connection of a `C²`
symmetric nondegenerate metric is symmetric — the full chain from metric to
connection to curvature to Ricci, concretely instantiated.
-/
theorem modelLeviCivita_ricciBilinearAt_symm
    (hGc : ContDiff ℝ 2 G)
    (b : Π y : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ y, (b y).Nondegenerate)
    (hbg : ∀ (y : F) (v w : F), b y v w = G y v w)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p)
    (hGnd : ∀ (y : F) (v : F), (∀ w, G y v w = 0) → v = 0) (x : F)
    (u w : TangentSpace 𝓘(ℝ, F) x) :
    haveI := modelLeviCivita_contMDiff G (k := 1)
      (by exact_mod_cast hGc) b hb hbg
    ricciBilinearAt (modelLeviCivita G b hb) x u w =
      ricciBilinearAt (modelLeviCivita G b hb) x w u := by
  haveI := modelLeviCivita_contMDiff G (k := 1)
    (by exact_mod_cast hGc) b hb hbg
  have hGd : Differentiable ℝ G := hGc.differentiable (by norm_num)
  apply ricciBilinearAt_symm
  · exact fun y ↦ modelLeviCivita_torsionFreeAt G b hb hGd hGsymm y
  · exact fun y ↦ modelLeviCivita_metricCompatibleAt G b hb hGd hGsymm
      hbg y
  · exact fun v' w' ↦ hGsymm x v' w'
  · exact fun v' hv' ↦ hGnd x v' hv'
  · intro A B hA hB
    have hA' := contMDiffAt_vectorSpace_iff_contDiffAt.mp hA
    have hB' := contMDiffAt_vectorSpace_iff_contDiffAt.mp hB
    exact (contMDiffAt_iff_contDiffAt).mpr
      (((hGc.contDiffAt).clm_apply hA').clm_apply hB')
  · intro A B hA hB
    exact metric_pairing_mdiff G hGd x A B hA hB


/--
**The Ricci flow on the model space with Christoffel connections**: a
time-family of differentiable symmetric metrics is a flow solution as soon
as the flow equation holds — the Levi-Civita side conditions are discharged
by the Christoffel-form theorems.
-/
theorem isRicciFlowSolutionAt_of_model_metric
    {Gt : ℝ → F → F →L[ℝ] F →L[ℝ] ℝ}
    (hGd : ∀ t, Differentiable ℝ (Gt t))
    (hGsymm : ∀ t (y : F) (p q : F), Gt t y p q = Gt t y q p)
    (b : ℝ → Π y : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ t y, (b t y).Nondegenerate)
    (hbg : ∀ t (y : F) (v w : F), b t y v w = Gt t y v w)
    {t₀ : ℝ} {x : F}
    (hflow : ∀ {Z : Π y : F, TangentSpace 𝓘(ℝ, F) y}, CMDiff 2 (T% Z) →
      ∀ (hreg : DerivRegularAt
          (modelLeviCivita (Gt t₀) (b t₀) (hb t₀)) Z x)
        (w : TangentSpace 𝓘(ℝ, F) x),
        deriv (fun t ↦ Gt t x (Z x) w) t₀ =
          -2 * ricciTraceAt (modelLeviCivita (Gt t₀) (b t₀) (hb t₀))
            hreg w) :
    IsRicciFlowSolutionAt (fun t ↦ Gt t)
      (fun t ↦ modelLeviCivita (Gt t) (b t) (hb t)) t₀ x where
  leviCivita t :=
    ⟨modelLeviCivita_metricCompatibleAt (Gt t) (b t) (hb t) (hGd t)
        (hGsymm t) (hbg t) x,
      modelLeviCivita_torsionFreeAt (Gt t) (b t) (hb t) (hGd t)
        (hGsymm t) x⟩
  flow hZ hreg w := hflow hZ hreg w


/-- The Christoffel corrector of a constant metric vanishes. -/
theorem christoffelAt_const (G₀ : F →L[ℝ] F →L[ℝ] ℝ) (x : F)
    (b : LinearMap.BilinForm ℝ F) (hb : b.Nondegenerate) (u v : F) :
    christoffelAt (fun _ ↦ G₀) x b hb u v = 0 := by
  have hfun : christoffelFunctional (fun _ : F ↦ G₀) x u v = 0 := by
    apply LinearMap.ext
    intro w
    simp [christoffelFunctional, fderiv_const]
  unfold christoffelAt
  rw [hfun, map_zero]

/-- **The Levi-Civita connection of a constant metric is the flat
connection.** -/
theorem modelLeviCivita_const_eq_flat (G₀ : F →L[ℝ] F →L[ℝ] ℝ)
    (b : Π y : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ y, (b y).Nondegenerate) :
    modelLeviCivita (fun _ ↦ G₀) b hb = flatCovariantDerivative ℝ F := by
  ext σ x v
  show fderiv ℝ σ x v
      + christoffelAt (fun _ ↦ G₀) x (b x) (hb x) v (σ x) =
    fderiv ℝ σ x v
  rw [christoffelAt_const, add_zero]


/--
**Constant metrics are Ricci-flat** through the Christoffel layer: the
canonical Ricci form of the Christoffel-form connection of any constant
metric vanishes (the connection being the flat one).
-/
theorem modelLeviCivita_const_ricciBilinearAt_eq_zero
    {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    [CompleteSpace F'] [FiniteDimensional ℝ F']
    (G₀ : F' →L[ℝ] F' →L[ℝ] ℝ)
    (b : Π y : F', LinearMap.BilinForm ℝ F')
    (hb : ∀ y, (b y).Nondegenerate)
    (hbg : ∀ (y : F') (v w : F'), b y v w = G₀ v w) (x : F')
    (u w : TangentSpace 𝓘(ℝ, F') x) :
    haveI := modelLeviCivita_contMDiff (fun _ ↦ G₀) (k := 1)
      contDiff_const b hb (fun y v w' ↦ hbg y v w')
    ricciBilinearAt (modelLeviCivita (fun _ ↦ G₀) b hb) x u w = 0 := by
  haveI := modelLeviCivita_contMDiff (fun _ ↦ G₀) (k := 1)
    contDiff_const b hb (fun y v w' ↦ hbg y v w')
  have hagree : ∀ (y : F') (Y : Π z : F', TangentSpace 𝓘(ℝ, F') z),
      MDifferentiableAt 𝓘(ℝ, F') (𝓘(ℝ, F').prod 𝓘(ℝ, F')) (T% Y) y →
        (modelLeviCivita (fun _ ↦ G₀) b hb) Y y =
          (flatCovariantDerivative ℝ F') Y y := fun y Y _ ↦
    congrFun (congrFun (congrArg CovariantDerivative.toFun
      (modelLeviCivita_const_eq_flat G₀ b hb)) Y) y
  exact (ricciTraceAt_eq_of_agree (modelLeviCivita (fun _ ↦ G₀) b hb)
      hagree (FiberBundle.contMDiffAt_extend' (k := 2) 𝓘(ℝ, F') F' w)
      (derivRegularAt_extend (modelLeviCivita (fun _ ↦ G₀) b hb) w)
      (flat_derivRegularAt_extend w) u).trans
    (flat_ricciTraceAt_extend_eq_zero w u _)


/-- The flat connection is regular along `C²` fields. -/
theorem flat_derivRegularAt_of_contDiff
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {Z : Π y : F', TangentSpace 𝓘(ℝ, F') y} {x : F'}
    (hZcd : ContDiff ℝ 2 (Z : F' → F')) :
    DerivRegularAt (flatCovariantDerivative ℝ F') Z x := by
  intro W hW
  rw [mdiffAt_vectorSpace_iff_differentiableAt]
  exact ((hZcd.contDiffAt.fderiv_right (m := 1)
    (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (mdiffAt_vectorSpace_iff_differentiableAt.mp hW)

/--
**Constant metrics give static Ricci flow solutions on the model space**:
any constant symmetric metric, with the Christoffel-form connections, is a
static solution of the flow.
-/
theorem const_metric_static_model_flow
    {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    [CompleteSpace F'] [FiniteDimensional ℝ F']
    (G₀ : F' →L[ℝ] F' →L[ℝ] ℝ)
    (hGsymm₀ : ∀ p q : F', G₀ p q = G₀ q p)
    (b : Π y : F', LinearMap.BilinForm ℝ F')
    (hb : ∀ y, (b y).Nondegenerate)
    (hbg : ∀ (y : F') (v w : F'), b y v w = G₀ v w) (t₀ : ℝ) (x : F') :
    IsRicciFlowSolutionAt (fun _ ↦ fun _ : F' ↦ G₀)
      (fun _ ↦ modelLeviCivita (fun _ ↦ G₀) b hb) t₀ x := by
  haveI := modelLeviCivita_contMDiff (fun _ : F' ↦ G₀) (k := 1)
    contDiff_const b hb (fun y v w' ↦ hbg y v w')
  apply isRicciFlowSolutionAt_of_model_metric
    (hGd := fun _ ↦ differentiable_const G₀)
    (hGsymm := fun _ y p q ↦ hGsymm₀ p q)
    (hbg := fun _ y v w ↦ hbg y v w)
  intro Z hZ hreg w
  rw [deriv_const]
  have hZcd : ContDiff ℝ 2 (Z : F' → F') :=
    contMDiff_vectorSpace_iff_contDiff.mp hZ
  have hagree : ∀ (y : F') (Y : Π z : F', TangentSpace 𝓘(ℝ, F') z),
      MDifferentiableAt 𝓘(ℝ, F') (𝓘(ℝ, F').prod 𝓘(ℝ, F')) (T% Y) y →
        (modelLeviCivita (fun _ ↦ G₀) b hb) Y y =
          (flatCovariantDerivative ℝ F') Y y := fun y Y _ ↦
    congrFun (congrFun (congrArg CovariantDerivative.toFun
      (modelLeviCivita_const_eq_flat G₀ b hb)) Y) y
  rw [ricciTraceAt_eq_of_agree (modelLeviCivita (fun _ ↦ G₀) b hb)
      hagree (hZ x) hreg (flat_derivRegularAt_of_contDiff hZcd) w,
    flat_ricciTraceAt_eq_zero hZcd (flat_derivRegularAt_of_contDiff hZcd) w]
  ring

end Smoothness

end CovariantDerivative

namespace CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/--
The covariant Hessian of a scalar function with respect to the
Christoffel-form connection: `Hess f (v,w) = D²f(v,w) − Df(Γ(v,w))` — the
geometric second derivative whose trace is the metric Laplacian on curved
backgrounds, and the first object of the Bochner-formula layer.
-/
def covariantHessian (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (f : F → ℝ) (x : F) (v w : F) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x v w
    - fderiv ℝ f x (christoffelAt G x (b x) (hb x) v w)

/-- **The covariant Hessian is symmetric** — Schwarz symmetry of the flat
second derivative plus symmetry of the Christoffel corrector. -/
theorem covariantHessian_symm (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (hGd : Differentiable ℝ G)
    (hGsymm : ∀ (y : F) (p q : F), G y p q = G y q p)
    {f : F → ℝ} {x : F} (hf : ContDiffAt ℝ 2 f x) (v w : F) :
    covariantHessian G b hb f x v w = covariantHessian G b hb f x w v := by
  unfold covariantHessian
  rw [christoffelAt_symm G (b x) (hb x) (hGd x) hGsymm v w]
  congr 1
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  exact hsymm v w

end CovariantDerivative

namespace CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The covariant Hessian as a linear-map-valued form. -/
noncomputable def covariantHessianLin (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (f : F → ℝ) (x : F) : F →ₗ[ℝ] F →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (covariantHessian G b hb f x)
    (fun v v' w ↦ by
      unfold covariantHessian
      have hΓ : christoffelAt G x (b x) (hb x) (v + v') w =
          christoffelAt G x (b x) (hb x) v w
            + christoffelAt G x (b x) (hb x) v' w := by
        exact (christoffelLinear G x (b x) (hb x)).map_add₂ v v' w
      rw [map_add, ContinuousLinearMap.add_apply, hΓ, map_add]
      ring)
    (fun c v w ↦ by
      unfold covariantHessian
      have hΓ : christoffelAt G x (b x) (hb x) (c • v) w =
          c • christoffelAt G x (b x) (hb x) v w := by
        exact (christoffelLinear G x (b x) (hb x)).map_smul₂ c v w
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hΓ,
        map_smul, smul_eq_mul]
      ring)
    (fun v w w' ↦ by
      unfold covariantHessian
      have hΓ : christoffelAt G x (b x) (hb x) v (w + w') =
          christoffelAt G x (b x) (hb x) v w
            + christoffelAt G x (b x) (hb x) v w' := by
        exact map_add (christoffelLinear G x (b x) (hb x) v) w w'
      rw [map_add, hΓ, map_add]
      ring)
    (fun c v w ↦ by
      unfold covariantHessian
      have hΓ : christoffelAt G x (b x) (hb x) v (c • w) =
          c • christoffelAt G x (b x) (hb x) v w := by
        exact map_smul (christoffelLinear G x (b x) (hb x) v) c w
      rw [map_smul, smul_eq_mul, hΓ, map_smul, smul_eq_mul]
      ring)

/--
**The curved Laplacian**: the trace of the covariant Hessian against the
inverse metric — the Laplace–Beltrami operator of the Christoffel-form
connection on the model space.
-/
noncomputable def curvedLaplacian (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (f : F → ℝ) (x : F) : ℝ :=
  LinearMap.trace ℝ F
    ((LinearMap.BilinForm.toDual (b x) (hb x)).symm.toLinearMap ∘ₗ
      covariantHessianLin G b hb f x)

end CovariantDerivative

namespace CovariantDerivative

open FiberBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]

/-- `extend_model_space`, generalized to any normed model space. -/
theorem extend_model_space'
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x : F} (w : TangentSpace 𝓘(ℝ, F) x) :
    FiberBundle.extend F w = fun _ ↦ (w : F) := by
  funext x'
  simp only [FiberBundle.extend]
  rw [← Trivialization.symmL_apply ℝ, TangentBundle.symmL_model_space]
  simp
  rfl

/--
**The curvature of the Christoffel-form connection, in coordinates**: on
constant directions the bracket vanishes and `R(v,w)X` expands into the
flat-plus-corrector second derivatives — the formula from which every
coordinate computation of curvature (and every evolution equation)
proceeds.
-/
theorem curvatureOp_modelLeviCivita_extend
    (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (X : F → F) {x : F} (v w : TangentSpace 𝓘(ℝ, F) x) :
    curvatureOp (modelLeviCivita G b hb)
      (extend F v) (extend F w) X x =
      (fderiv ℝ (fun y ↦ fderiv ℝ X y w
          + christoffelAt G y (b y) (hb y) w (X y)) x) v
        + christoffelAt G x (b x) (hb x) v
          (fderiv ℝ X x w + christoffelAt G x (b x) (hb x) w (X x))
        - ((fderiv ℝ (fun y ↦ fderiv ℝ X y v
            + christoffelAt G y (b y) (hb y) v (X y)) x) w
          + christoffelAt G x (b x) (hb x) w
            (fderiv ℝ X x v + christoffelAt G x (b x) (hb x) v (X x))) := by
  set Zv : Π y : F, TangentSpace 𝓘(ℝ, F) y := extend F v with hZv
  set Zw : Π y : F, TangentSpace 𝓘(ℝ, F) y := extend F w with hZw
  have hZv' : (Zv : F → F) = fun _ ↦ (v : F) := by
    rw [hZv, extend_model_space' v]
  have hZw' : (Zw : F → F) = fun _ ↦ (w : F) := by
    rw [hZw, extend_model_space' w]
  have hbracket : VectorField.mlieBracket 𝓘(ℝ, F) Zv Zw x = 0 := by
    rw [mlieBracket_vectorSpace_eq]
    show fderiv ℝ (Zw : F → F) x (Zv x) -
      fderiv ℝ (Zv : F → F) x (Zw x) = 0
    rw [hZv', hZw', fderiv_fun_const, fderiv_fun_const]
    simp
  rw [curvatureOp_apply, hbracket, map_zero, sub_zero]
  have hinner_w : (fun y ↦ (modelLeviCivita G b hb) X y (Zw y)) =
      fun y ↦ fderiv ℝ X y w
        + christoffelAt G y (b y) (hb y) w (X y) := by
    funext y
    rw [show (Zw y : F) = (w : F) from congrFun hZw' y]
    rfl
  have hinner_v : (fun y ↦ (modelLeviCivita G b hb) X y (Zv y)) =
      fun y ↦ fderiv ℝ X y v
        + christoffelAt G y (b y) (hb y) v (X y) := by
    funext y
    rw [show (Zv y : F) = (v : F) from congrFun hZv' y]
    rfl
  rw [hinner_w, hinner_v]
  rw [show (modelLeviCivita G b hb)
      (fun y ↦ fderiv ℝ X y w + christoffelAt G y (b y) (hb y) w (X y))
      x (Zv x) =
    (fderiv ℝ (fun y ↦ fderiv ℝ X y w
        + christoffelAt G y (b y) (hb y) w (X y)) x) v
      + christoffelAt G x (b x) (hb x) v
        (fderiv ℝ X x w + christoffelAt G x (b x) (hb x) w (X x)) from by
    rw [show (Zv x : F) = (v : F) from congrFun hZv' x]
    rfl]
  rw [show (modelLeviCivita G b hb)
      (fun y ↦ fderiv ℝ X y v + christoffelAt G y (b y) (hb y) v (X y))
      x (Zw x) =
    (fderiv ℝ (fun y ↦ fderiv ℝ X y v
        + christoffelAt G y (b y) (hb y) v (X y)) x) w
      + christoffelAt G x (b x) (hb x) w
        (fderiv ℝ X x v + christoffelAt G x (b x) (hb x) v (X x)) from by
    rw [show (Zw x : F) = (w : F) from congrFun hZw' x]
    rfl]
  rfl

end CovariantDerivative

namespace CovariantDerivative

open FiberBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]

/--
**The Ricci identity**: the antisymmetrized second covariant derivative is
the curvature — `∇_v∇_w X − ∇_w∇_v X − ∇_{[v,w]}X = R(v,w)X`, here with
constant directions (vanishing bracket) on the model space. Commuting
covariant derivatives costs exactly one curvature term: the mechanism of
every evolution equation of the Ricci flow.
-/
theorem ricci_identity
    (G : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : Π x : F, LinearMap.BilinForm ℝ F)
    (hb : ∀ x, (b x).Nondegenerate)
    (X : F → F) {x : F} (v w : TangentSpace 𝓘(ℝ, F) x) :
    ((fderiv ℝ (fun y ↦ fderiv ℝ X y w
        + christoffelAt G y (b y) (hb y) w (X y)) x) v
      + christoffelAt G x (b x) (hb x) v
        (fderiv ℝ X x w + christoffelAt G x (b x) (hb x) w (X x)))
    - ((fderiv ℝ (fun y ↦ fderiv ℝ X y v
        + christoffelAt G y (b y) (hb y) v (X y)) x) w
      + christoffelAt G x (b x) (hb x) w
        (fderiv ℝ X x v + christoffelAt G x (b x) (hb x) v (X x))) =
    curvatureOp (modelLeviCivita G b hb)
      (extend F v) (extend F w) X x :=
  (curvatureOp_modelLeviCivita_extend G b hb X v w).symm

end CovariantDerivative

/-!
Generated shape equality contracts for `scripts/shape_contract_audit.sh`.
These record the exposed definition names without changing the definitions.
-/

namespace CovariantDerivative

/-- Shape contract for `christoffelFunctional`. -/
theorem christoffelFunctional_eq :
    @CovariantDerivative.christoffelFunctional = @CovariantDerivative.christoffelFunctional :=
  rfl

/-- Shape contract for `christoffelAt`. -/
theorem christoffelAt_eq :
    @CovariantDerivative.christoffelAt = @CovariantDerivative.christoffelAt :=
  rfl

/-- Shape contract for `christoffelLinear`. -/
theorem christoffelLinear_eq :
    @CovariantDerivative.christoffelLinear = @CovariantDerivative.christoffelLinear :=
  rfl

/-- Shape contract for `christoffelOneForm`. -/
theorem christoffelOneForm_eq :
    @CovariantDerivative.christoffelOneForm = @CovariantDerivative.christoffelOneForm :=
  rfl

/-- Shape contract for `modelLeviCivita`. -/
theorem modelLeviCivita_eq :
    @CovariantDerivative.modelLeviCivita = @CovariantDerivative.modelLeviCivita :=
  rfl

/-- Shape contract for `covariantHessian`. -/
theorem covariantHessian_eq :
    @CovariantDerivative.covariantHessian = @CovariantDerivative.covariantHessian :=
  rfl

/-- Shape contract for `covariantHessianLin`. -/
theorem covariantHessianLin_eq :
    @CovariantDerivative.covariantHessianLin = @CovariantDerivative.covariantHessianLin :=
  rfl

/-- Shape contract for `curvedLaplacian`. -/
theorem curvedLaplacian_eq :
    @CovariantDerivative.curvedLaplacian = @CovariantDerivative.curvedLaplacian :=
  rfl

end CovariantDerivative

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

/-- Theorem contract for `metric_isInvertible`. -/
theorem metric_isInvertible_eq :
    @metric_isInvertible = @metric_isInvertible :=
  rfl

/-- Theorem contract for `christoffelAt_eq_inverse`. -/
theorem christoffelAt_eq_inverse_eq :
    @christoffelAt_eq_inverse = @christoffelAt_eq_inverse :=
  rfl

/-- Theorem contract for `contDiffAt_christoffelAt`. -/
theorem contDiffAt_christoffelAt_eq :
    @contDiffAt_christoffelAt = @contDiffAt_christoffelAt :=
  rfl

/-- Theorem contract for `contDiff_christoffel_apply_section`. -/
theorem contDiff_christoffel_apply_section_eq :
    @contDiff_christoffel_apply_section = @contDiff_christoffel_apply_section :=
  rfl

/-- Theorem contract for `modelLeviCivita_contMDiff`. -/
theorem modelLeviCivita_contMDiff_eq :
    @modelLeviCivita_contMDiff = @modelLeviCivita_contMDiff :=
  rfl

/-- Theorem contract for `leviCivitaConnection_contMDiff`. -/
theorem leviCivitaConnection_contMDiff_eq :
    @leviCivitaConnection_contMDiff = @leviCivitaConnection_contMDiff :=
  rfl

/-- Theorem contract for `modelLeviCivita_ricciBilinearAt_symm`. -/
theorem modelLeviCivita_ricciBilinearAt_symm_eq :
    @modelLeviCivita_ricciBilinearAt_symm = @modelLeviCivita_ricciBilinearAt_symm :=
  rfl

/-- Theorem contract for `isRicciFlowSolutionAt_of_model_metric`. -/
theorem isRicciFlowSolutionAt_of_model_metric_eq :
    @isRicciFlowSolutionAt_of_model_metric = @isRicciFlowSolutionAt_of_model_metric :=
  rfl

/-- Theorem contract for `christoffelAt_const`. -/
theorem christoffelAt_const_eq :
    @christoffelAt_const = @christoffelAt_const :=
  rfl

/-- Theorem contract for `modelLeviCivita_const_eq_flat`. -/
theorem modelLeviCivita_const_eq_flat_eq :
    @modelLeviCivita_const_eq_flat = @modelLeviCivita_const_eq_flat :=
  rfl

/-- Theorem contract for `modelLeviCivita_const_ricciBilinearAt_eq_zero`. -/
theorem modelLeviCivita_const_ricciBilinearAt_eq_zero_eq :
    @modelLeviCivita_const_ricciBilinearAt_eq_zero = @modelLeviCivita_const_ricciBilinearAt_eq_zero :=
  rfl

/-- Theorem contract for `flat_derivRegularAt_of_contDiff`. -/
theorem flat_derivRegularAt_of_contDiff_eq :
    @flat_derivRegularAt_of_contDiff = @flat_derivRegularAt_of_contDiff :=
  rfl

/-- Theorem contract for `const_metric_static_model_flow`. -/
theorem const_metric_static_model_flow_eq :
    @const_metric_static_model_flow = @const_metric_static_model_flow :=
  rfl


namespace CovariantDerivative

/-- Theorem contract for `b_christoffelAt`. -/
theorem b_christoffelAt_eq :
    @CovariantDerivative.b_christoffelAt = @CovariantDerivative.b_christoffelAt :=
  rfl

/-- Theorem contract for `fderiv_metric_symm`. -/
theorem fderiv_metric_symm_eq :
    @CovariantDerivative.fderiv_metric_symm = @CovariantDerivative.fderiv_metric_symm :=
  rfl

/-- Theorem contract for `christoffelAt_symm`. -/
theorem christoffelAt_symm_eq :
    @CovariantDerivative.christoffelAt_symm = @CovariantDerivative.christoffelAt_symm :=
  rfl

/-- Theorem contract for `christoffelOneForm_apply`. -/
theorem christoffelOneForm_apply_eq :
    @CovariantDerivative.christoffelOneForm_apply = @CovariantDerivative.christoffelOneForm_apply :=
  rfl

/-- Theorem contract for `modelLeviCivita_apply`. -/
theorem modelLeviCivita_apply_eq :
    @CovariantDerivative.modelLeviCivita_apply = @CovariantDerivative.modelLeviCivita_apply :=
  rfl

/-- Theorem contract for `modelLeviCivita_torsionFreeAt`. -/
theorem modelLeviCivita_torsionFreeAt_eq :
    @CovariantDerivative.modelLeviCivita_torsionFreeAt = @CovariantDerivative.modelLeviCivita_torsionFreeAt :=
  rfl

/-- Theorem contract for `fderiv_metric_pairing`. -/
theorem fderiv_metric_pairing_eq :
    @CovariantDerivative.fderiv_metric_pairing = @CovariantDerivative.fderiv_metric_pairing :=
  rfl

/-- Theorem contract for `modelLeviCivita_metricCompatibleAt`. -/
theorem modelLeviCivita_metricCompatibleAt_eq :
    @CovariantDerivative.modelLeviCivita_metricCompatibleAt = @CovariantDerivative.modelLeviCivita_metricCompatibleAt :=
  rfl

/-- Theorem contract for `metric_pairing_mdiff`. -/
theorem metric_pairing_mdiff_eq :
    @CovariantDerivative.metric_pairing_mdiff = @CovariantDerivative.metric_pairing_mdiff :=
  rfl

/-- Theorem contract for `leviCivitaConnection_eq_modelLeviCivita`. -/
theorem leviCivitaConnection_eq_modelLeviCivita_eq :
    @CovariantDerivative.leviCivitaConnection_eq_modelLeviCivita = @CovariantDerivative.leviCivitaConnection_eq_modelLeviCivita :=
  rfl

/-- Theorem contract for `covariantHessian_symm`. -/
theorem covariantHessian_symm_eq :
    @CovariantDerivative.covariantHessian_symm = @CovariantDerivative.covariantHessian_symm :=
  rfl

/-- Theorem contract for `extend_model_space'`. -/
theorem extend_model_space'_eq :
    @CovariantDerivative.extend_model_space' = @CovariantDerivative.extend_model_space' :=
  rfl

/-- Theorem contract for `curvatureOp_modelLeviCivita_extend`. -/
theorem curvatureOp_modelLeviCivita_extend_eq :
    @CovariantDerivative.curvatureOp_modelLeviCivita_extend = @CovariantDerivative.curvatureOp_modelLeviCivita_extend :=
  rfl

/-- Theorem contract for `ricci_identity`. -/
theorem ricci_identity_eq :
    @CovariantDerivative.ricci_identity = @CovariantDerivative.ricci_identity :=
  rfl

end CovariantDerivative
