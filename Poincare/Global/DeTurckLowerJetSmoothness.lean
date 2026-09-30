import Poincare.Global.DeTurckPrincipalIdentity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open scoped ContDiff BigOperators

namespace Poincare.DeTurckLowerJetSmoothness
open DeTurckPrincipalSecondJet DeTurckPrincipalIdentity

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

private theorem contDiffAt_clm_of_apply
    {D V W : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : WithTop ENat} {f : D → V →L[ℝ] W} {x : D}
    (h : ∀ v, ContDiffAt ℝ n (fun y => f y v) x) : ContDiffAt ℝ n f x := by
  let d := Module.finrank ℝ V
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : W ≃L[ℝ] W)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp x (contDiffAt_pi.mpr (fun i => h _))

private theorem contDiffAt_koszul
    {p0 : Bilin × Jet1} {u v : Bilin × Jet1 → E}
    (hu : ContDiffAt ℝ ∞ u p0) (hv : ContDiffAt ℝ ∞ v p0) :
    ContDiffAt ℝ ∞ (fun p => koszul p.2 (u p) (v p)) p0 := by
  apply contDiffAt_clm_of_apply
  intro q
  simp only [koszul_apply]
  exact contDiffAt_const.mul
    ((((contDiffAt_snd.clm_apply hu).clm_apply hv).clm_apply contDiffAt_const).add
      (((contDiffAt_snd.clm_apply hv).clm_apply hu).clm_apply contDiffAt_const) |>.sub
      (((contDiffAt_snd.clm_apply contDiffAt_const).clm_apply hu).clm_apply hv))

private theorem contDiffAt_connection
    {p0 : Bilin × Jet1} (hG : p0.1.IsInvertible) {u v : Bilin × Jet1 → E}
    (hu : ContDiffAt ℝ ∞ u p0) (hv : ContDiffAt ℝ ∞ v p0) :
    ContDiffAt ℝ ∞ (fun p => connection p.1 p.2 (u p) (v p)) p0 := by
  exact (hG.contDiffAt_map_inverse.comp p0 contDiffAt_fst).clm_apply
    (contDiffAt_koszul hv hu)

private theorem contDiffAt_fieldValue
    {p0 : Bilin × Jet1} (hG : p0.1.IsInvertible) (B : E →L[ℝ] E →L[ℝ] E) :
    ContDiffAt ℝ ∞ (fun p => fieldValue p.1 p.2 B) p0 := by
  unfold fieldValue
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun p : Bilin × Jet1 => p.1.inverse) p0 :=
    hG.contDiffAt_map_inverse.comp p0 contDiffAt_fst
  have hr := hi.clm_apply
    (contDiffAt_const (c := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
  exact (contDiffAt_connection hG hr contDiffAt_const).sub
    ((contDiffAt_const.clm_apply hr).clm_apply contDiffAt_const)

private theorem contDiffAt_fieldFirst
    {p0 : Bilin × Jet1} (hG : p0.1.IsInvertible)
    (B : E →L[ℝ] E →L[ℝ] E) (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (a : E) :
    ContDiffAt ℝ ∞ (fun p => fieldFirst p.1 p.2 B DB a) p0 := by
  unfold fieldFirst
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun p : Bilin × Jet1 => p.1.inverse) p0 :=
    hG.contDiffAt_map_inverse.comp p0 contDiffAt_fst
  have hr := hi.clm_apply
    (contDiffAt_const (c := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
  have hdr := (hi.clm_apply ((contDiffAt_snd.clm_apply
    (contDiffAt_const (c := a))).clm_apply hr)).neg
  have hc := contDiffAt_connection hG hr
    (contDiffAt_const (c := (Module.finBasis ℝ E) i))
  exact (((hi.clm_apply ((contDiffAt_snd.clm_apply contDiffAt_const).clm_apply hc)).neg.add
    (contDiffAt_connection hG hdr contDiffAt_const)).sub
    (((contDiffAt_const.clm_apply contDiffAt_const).clm_apply hr).clm_apply contDiffAt_const)).sub
    ((contDiffAt_const.clm_apply hdr).clm_apply contDiffAt_const)

private theorem contDiffAt_ricciFirst
    {p0 : Bilin × Jet1} (hG : p0.1.IsInvertible) (v w : E) :
    ContDiffAt ℝ ∞ (fun p => ricciFirst p.1 p.2 v w) p0 := by
  unfold ricciFirst
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun p : Bilin × Jet1 => p.1.inverse) p0 :=
    hG.contDiffAt_map_inverse.comp p0 contDiffAt_fst
  have cvw := contDiffAt_connection hG
    (contDiffAt_const (c := v)) (contDiffAt_const (c := w))
  have ciw := contDiffAt_connection hG
    (contDiffAt_const (c := (Module.finBasis ℝ E) i)) (contDiffAt_const (c := w))
  apply (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contDiff.contDiffAt.comp p0
  exact (((hi.clm_apply ((contDiffAt_snd.clm_apply contDiffAt_const).clm_apply cvw)).neg.add
    (hi.clm_apply ((contDiffAt_snd.clm_apply contDiffAt_const).clm_apply ciw))).add
    (contDiffAt_connection hG contDiffAt_const cvw)).sub
    (contDiffAt_connection hG contDiffAt_const ciw)

/-- The actual DeTurck lower coefficient is smooth near every invertible metric jet.
This supplies finite-jet differentiability for the subsequent full linearization. -/
theorem contDiffAt_lowerTerm :
    letI : NormedAddCommGroup Jet1 :=
      ContinuousLinearMap.toNormedAddCommGroup
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
    letI : NormedSpace ℝ Jet1 :=
      ContinuousLinearMap.toNormedSpace
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
        (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
    ∀ (B : E →L[ℝ] E →L[ℝ] E) (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
      (G0 : Bilin) (J0 : Jet1), G0.IsInvertible →
    ContDiffAt ℝ ∞ (fun p : Bilin × Jet1 => lowerTerm B DB p.1 p.2) (G0, J0) := by
  intro B DB G0 J0 hG
  apply contDiffAt_clm_of_apply
  intro v
  apply contDiffAt_clm_of_apply
  intro w
  simp only [lowerTerm_apply, lieFirst]
  exact (contDiffAt_const.mul (contDiffAt_ricciFirst hG v w)).add
    (((((contDiffAt_snd.clm_apply (contDiffAt_fieldValue hG B)).clm_apply
      contDiffAt_const).clm_apply contDiffAt_const).add
      ((contDiffAt_fst.clm_apply (contDiffAt_fieldFirst hG B DB v)).clm_apply contDiffAt_const)).add
      ((contDiffAt_fst.clm_apply contDiffAt_const).clm_apply (contDiffAt_fieldFirst hG B DB w)))

end Poincare.DeTurckLowerJetSmoothness
