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

end Smoothness

end CovariantDerivative
