import Poincare.Global.DeTurckChartIndependentPullback
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pullback preserves equality of two-jets

The bilinear pullback depends on the coefficient field and on both slots of
the coordinate differential. Its second derivative therefore uses the third
derivative of the coordinate map.
-/

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Poincare.DeTurckPullbackTwoJet

section ChainRule

variable {E X Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Differentiate the first chain rule as an identity of derivative fields.
The first-derivative identity holds on a neighborhood before it is used for
the second derivative. -/
theorem fderiv_fderiv_comp (f : X → Y) (g : E → X) (x : E)
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f (g y))) x =
      (ContinuousLinearMap.compL ℝ E X Y (fderiv ℝ f (g x))).comp
          (fderiv ℝ (fderiv ℝ g) x) +
        ((ContinuousLinearMap.compL ℝ E X Y).flip (fderiv ℝ g x)).comp
          ((fderiv ℝ (fderiv ℝ f) (g x)).comp (fderiv ℝ g x)) := by
  have hfg : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (g y) :=
    hg.continuousAt.eventually (hf.eventually (by simp))
  have heq : fderiv ℝ (fun y => f (g y)) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ f (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [hfg, hg.eventually (by simp)] with y hfy hgy
    exact fderiv_comp y (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (g x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgc : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  rw [heq.fderiv_eq]
  simpa only [Function.comp_def] using
    (hdf.hasFDerivAt.comp x hgc.hasFDerivAt |>.clm_comp hdg.hasFDerivAt).fderiv

/-- Composition preserves matched value, first derivative and second
derivative, allowing both the outer and inner functions to vary. -/
theorem comp_twoJet_congr (f₁ f₂ : X → Y) (g₁ g₂ : E → X) (x : E)
    (hf₁ : ContDiffAt ℝ 2 f₁ (g₁ x))
    (hf₂ : ContDiffAt ℝ 2 f₂ (g₂ x))
    (hg₁ : ContDiffAt ℝ 2 g₁ x) (hg₂ : ContDiffAt ℝ 2 g₂ x)
    (hg1 : fderiv ℝ g₁ x = fderiv ℝ g₂ x)
    (hg2 : fderiv ℝ (fderiv ℝ g₁) x = fderiv ℝ (fderiv ℝ g₂) x)
    (hf0 : f₁ (g₁ x) = f₂ (g₂ x))
    (hf1 : fderiv ℝ f₁ (g₁ x) = fderiv ℝ f₂ (g₂ x))
    (hf2 : fderiv ℝ (fderiv ℝ f₁) (g₁ x) =
      fderiv ℝ (fderiv ℝ f₂) (g₂ x)) :
    (fun y => f₁ (g₁ y)) x = (fun y => f₂ (g₂ y)) x ∧
      fderiv ℝ (fun y => f₁ (g₁ y)) x =
        fderiv ℝ (fun y => f₂ (g₂ y)) x ∧
      fderiv ℝ (fderiv ℝ (fun y => f₁ (g₁ y))) x =
        fderiv ℝ (fderiv ℝ (fun y => f₂ (g₂ y))) x := by
  refine ⟨hf0, ?_, ?_⟩
  · change fderiv ℝ (f₁ ∘ g₁) x = fderiv ℝ (f₂ ∘ g₂) x
    rw [fderiv_comp x (hf₁.differentiableAt (by norm_num))
      (hg₁.differentiableAt (by norm_num)),
      fderiv_comp x (hf₂.differentiableAt (by norm_num))
        (hg₂.differentiableAt (by norm_num)), hf1, hg1]
  · rw [fderiv_fderiv_comp f₁ g₁ x hf₁ hg₁,
      fderiv_fderiv_comp f₂ g₂ x hf₂ hg₂, hf1, hf2, hg1, hg2]

end ChainRule

section Products

variable {E X Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The whole second derivative of a paired field. -/
theorem fderiv_fderiv_prodMk (f : E → X) (g : E → Y) (x : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => (f y, g y))) x =
      ((ContinuousLinearMap.prodₗᵢ ℝ (E := E) (F := X) (G := Y)).toContinuousLinearEquiv.toContinuousLinearMap).comp
          ((fderiv ℝ (fderiv ℝ f) x).prod (fderiv ℝ (fderiv ℝ g) x)) := by
  let L : ((E →L[ℝ] X) × (E →L[ℝ] Y)) →L[ℝ] (E →L[ℝ] X × Y) :=
    (ContinuousLinearMap.prodₗᵢ ℝ (𝕜 := ℝ) (E := E) (F := X) (G := Y)).toContinuousLinearEquiv.toContinuousLinearMap
  have heq : fderiv ℝ (fun y => (f y, g y)) =ᶠ[𝓝 x]
      fun y => L (fderiv ℝ f y, fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
    exact (hfy.differentiableAt (by norm_num)).fderiv_prodMk
      (hgy.differentiableAt (by norm_num))
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [heq.fderiv_eq]
  exact (L.hasFDerivAt.comp x (hdf.hasFDerivAt.prodMk hdg.hasFDerivAt)).fderiv

end Products

universe u

/-- The pullback operation is smooth in the coefficient and the map used in
both tensor slots. This statement uses the existing nested operator norms. -/
theorem contDiff_pullbackBilinearForm
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContDiff ℝ 2 (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
      Poincare.pullbackBilinearForm p.1 p.2) := by
  letI pullbackTwoJetPrecompInnerGroup :
      NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E →L[ℝ] E) (F := E →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI pullbackTwoJetPrecompInnerSpace :
      NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
      (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E →L[ℝ] E) (F := E →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
  letI pullbackTwoJetPrecompGroup :
      NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := (E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI pullbackTwoJetPrecompSpace :
      NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
      (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := (E →L[ℝ] E) →L[ℝ] E →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
  letI pullbackTwoJetFlipGroup :
      NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E →L[ℝ] E) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI pullbackTwoJetFlipSpace :
      NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
      (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E →L[ℝ] E) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
  have hpre : ContDiff ℝ 2 (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
      ContinuousLinearMap.precompR E p.1) := by
    exact contDiff_const.clm_comp contDiff_fst
  have hflip : ContDiff ℝ 2 (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
      (ContinuousLinearMap.precompR E p.1).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E (E →L[ℝ] E) (E →L[ℝ] ℝ)).contDiff.comp hpre
  exact (hflip.clm_apply contDiff_snd).clm_comp contDiff_snd

/-- Equality of the value and both ordinary derivatives is preserved under
bilinear pullback. The C3 coordinate map supplies C2 for its Jacobian field. -/
theorem pullback_twoJet_congr
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h F : E → (E →L[ℝ] E →L[ℝ] ℝ)) (phi : E → E) (z : E)
    (hh : ContDiffAt ℝ 2 h (phi z)) (hF : ContDiffAt ℝ 2 F (phi z))
    (hphi : ContDiffAt ℝ 3 phi z)
    (h0 : h (phi z) = F (phi z))
    (h1 : fderiv ℝ h (phi z) = fderiv ℝ F (phi z))
    (h2 : fderiv ℝ (fderiv ℝ h) (phi z) = fderiv ℝ (fderiv ℝ F) (phi z)) :
    let T := fun (q : E → (E →L[ℝ] E →L[ℝ] ℝ)) (y : E) =>
      Poincare.pullbackBilinearForm (q (phi y)) (fderiv ℝ phi y)
    T h z = T F z ∧ fderiv ℝ (T h) z = fderiv ℝ (T F) z ∧
      fderiv ℝ (fderiv ℝ (T h)) z = fderiv ℝ (fderiv ℝ (T F)) z := by
  have hp : ContDiffAt ℝ 2 phi z := hphi.of_le (by norm_num)
  have hJ : ContDiffAt ℝ 2 (fderiv ℝ phi) z :=
    hphi.fderiv_right (by norm_num)
  obtain ⟨hc0, hc1, hc2⟩ := comp_twoJet_congr h F phi phi z
    hh hF hp hp rfl rfl h0 h1 h2
  let qh := fun y => (h (phi y), fderiv ℝ phi y)
  let qF := fun y => (F (phi y), fderiv ℝ phi y)
  have hqh : ContDiffAt ℝ 2 qh z := (hh.comp z hp).prodMk hJ
  have hqF : ContDiffAt ℝ 2 qF z := (hF.comp z hp).prodMk hJ
  have hq0 : qh z = qF z := by simp only [qh, qF, hc0]
  have hq1 : fderiv ℝ qh z = fderiv ℝ qF z := by
    change fderiv ℝ (fun y => ((h ∘ phi) y, fderiv ℝ phi y)) z =
      fderiv ℝ (fun y => ((F ∘ phi) y, fderiv ℝ phi y)) z
    rw [((hh.comp z hp).differentiableAt (by norm_num)).fderiv_prodMk
        (hJ.differentiableAt (by norm_num)),
      ((hF.comp z hp).differentiableAt (by norm_num)).fderiv_prodMk
        (hJ.differentiableAt (by norm_num))]
    exact congrArg (fun D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ =>
      D.prod (fderiv ℝ (fderiv ℝ phi) z)) hc1
  have hq2 : fderiv ℝ (fderiv ℝ qh) z = fderiv ℝ (fderiv ℝ qF) z := by
    rw [fderiv_fderiv_prodMk (fun y => h (phi y)) (fderiv ℝ phi) z
        (hh.comp z hp) hJ,
      fderiv_fderiv_prodMk (fun y => F (phi y)) (fderiv ℝ phi) z
        (hF.comp z hp) hJ, hc2]
  let P := fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
    Poincare.pullbackBilinearForm p.1 p.2
  have hP : ContDiff ℝ 2 P := contDiff_pullbackBilinearForm E
  exact comp_twoJet_congr P P qh qF z hP.contDiffAt hP.contDiffAt hqh hqF
    hq1 hq2 (congrArg P hq0) (congrArg (fderiv ℝ P) hq0)
    (congrArg (fderiv ℝ (fderiv ℝ P)) hq0)

end Poincare.DeTurckPullbackTwoJet
