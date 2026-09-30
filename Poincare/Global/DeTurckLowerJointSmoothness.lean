import Poincare.Global.DeTurckLowerJetSmoothness

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open scoped ContDiff BigOperators

namespace Poincare.DeTurckLowerJointSmoothness
open DeTurckPrincipalSecondJet DeTurckPrincipalIdentity

private abbrev BG := E →L[ℝ] E →L[ℝ] E
private abbrev DBSpace := E →L[ℝ] E →L[ℝ] E →L[ℝ] E

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup BG :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := (E →L[ℝ] E)) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ BG :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := (E →L[ℝ] E))
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup DBSpace :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := (E →L[ℝ] E →L[ℝ] E))
    (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ DBSpace :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := (E →L[ℝ] E →L[ℝ] E))
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

section Compositions
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {x : D} {G : D → Bilin} {J : D → Jet1} {B : D → BG} {DB : D → DBSpace}

private theorem contDiffAt_koszul
    (hJ : ContDiffAt ℝ ∞ J x) {u v : D → E}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) :
    ContDiffAt ℝ ∞ (fun p => koszul (J p) (u p) (v p)) x := by
  apply contDiffAt_clm_of_apply
  intro q
  simp only [koszul_apply]
  exact contDiffAt_const.mul
    ((((hJ.clm_apply hu).clm_apply hv).clm_apply contDiffAt_const).add
      (((hJ.clm_apply hv).clm_apply hu).clm_apply contDiffAt_const) |>.sub
      (((hJ.clm_apply contDiffAt_const).clm_apply hu).clm_apply hv))

private theorem contDiffAt_connection
    (hInv : (G x).IsInvertible) (hG : ContDiffAt ℝ ∞ G x)
    (hJ : ContDiffAt ℝ ∞ J x) {u v : D → E}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) :
    ContDiffAt ℝ ∞ (fun p => connection (G p) (J p) (u p) (v p)) x := by
  exact (hInv.contDiffAt_map_inverse.comp x hG).clm_apply
    (contDiffAt_koszul hJ hv hu)

private theorem contDiffAt_fieldValue
    (hInv : (G x).IsInvertible) (hG : ContDiffAt ℝ ∞ G x)
    (hJ : ContDiffAt ℝ ∞ J x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (fun p => fieldValue (G p) (J p) (B p)) x := by
  unfold fieldValue
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun p => (G p).inverse) x :=
    hInv.contDiffAt_map_inverse.comp x hG
  have hr := hi.clm_apply
    (contDiffAt_const (c := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
  exact (contDiffAt_connection hInv hG hJ hr contDiffAt_const).sub
    ((hB.clm_apply hr).clm_apply contDiffAt_const)

private theorem contDiffAt_fieldFirst
    (hInv : (G x).IsInvertible) (hG : ContDiffAt ℝ ∞ G x)
    (hJ : ContDiffAt ℝ ∞ J x) (hB : ContDiffAt ℝ ∞ B x)
    (hDB : ContDiffAt ℝ ∞ DB x) (a : E) :
    ContDiffAt ℝ ∞ (fun p => fieldFirst (G p) (J p) (B p) (DB p) a) x := by
  unfold fieldFirst
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun p => (G p).inverse) x :=
    hInv.contDiffAt_map_inverse.comp x hG
  have hr := hi.clm_apply
    (contDiffAt_const (c := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)))
  have hdr := (hi.clm_apply ((hJ.clm_apply
    (contDiffAt_const (c := a))).clm_apply hr)).neg
  have hc := contDiffAt_connection hInv hG hJ hr
    (contDiffAt_const (c := (Module.finBasis ℝ E) i))
  exact (((hi.clm_apply ((hJ.clm_apply contDiffAt_const).clm_apply hc)).neg.add
    (contDiffAt_connection hInv hG hJ hdr contDiffAt_const)).sub
    (((hDB.clm_apply contDiffAt_const).clm_apply hr).clm_apply contDiffAt_const)).sub
    ((hB.clm_apply hdr).clm_apply contDiffAt_const)

private theorem contDiffAt_ricciFirst
    (hInv : (G x).IsInvertible) (hG : ContDiffAt ℝ ∞ G x)
    (hJ : ContDiffAt ℝ ∞ J x) (v w : E) :
    ContDiffAt ℝ ∞ (fun p => ricciFirst (G p) (J p) v w) x := by
  unfold ricciFirst
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun p => (G p).inverse) x :=
    hInv.contDiffAt_map_inverse.comp x hG
  have cvw := contDiffAt_connection hInv hG hJ
    (contDiffAt_const (c := v)) (contDiffAt_const (c := w))
  have ciw := contDiffAt_connection hInv hG hJ
    (contDiffAt_const (c := (Module.finBasis ℝ E) i)) (contDiffAt_const (c := w))
  apply (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contDiff.contDiffAt.comp x
  exact (((hi.clm_apply ((hJ.clm_apply contDiffAt_const).clm_apply cvw)).neg.add
    (hi.clm_apply ((hJ.clm_apply contDiffAt_const).clm_apply ciw))).add
    (contDiffAt_connection hInv hG hJ contDiffAt_const cvw)).sub
    (contDiffAt_connection hInv hG hJ contDiffAt_const ciw)

end Compositions

/-- Joint smoothness of the actual lower term, including varying background jets.
This removes the coefficient regularity obstacle before the full DeTurck differential
and the global linear operator used to construct the Hamilton flow inputs. -/
theorem contDiffAt_lowerTerm_joint :
    letI : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedAddCommGroup
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ);
    letI : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedSpace
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
    letI : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ);
    letI : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
    letI : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ);
    letI : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
    ∀ (B : (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (DB : (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (G0 : Poincare.DeTurckPrincipalSecondJet.Bilin) (J0 : Poincare.DeTurckPrincipalSecondJet.Jet1),
    G0.IsInvertible → ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
     (fun p : ((Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) × (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) × (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) =>
       Poincare.DeTurckPrincipalIdentity.lowerTerm p.1.1 p.1.2 p.2.1 p.2.2)
     ((B,DB),(G0,J0)) := by
  intro B DB G0 J0 hInv
  let p0 : (BG × DBSpace) × (Bilin × Jet1) := ((B, DB), (G0, J0))
  have hG : ContDiffAt ℝ ∞ (fun p : (BG × DBSpace) × (Bilin × Jet1) => p.2.1) p0 :=
    contDiffAt_fst.comp p0 contDiffAt_snd
  have hJ : ContDiffAt ℝ ∞ (fun p : (BG × DBSpace) × (Bilin × Jet1) => p.2.2) p0 :=
    contDiffAt_snd.comp p0 contDiffAt_snd
  have hB : ContDiffAt ℝ ∞ (fun p : (BG × DBSpace) × (Bilin × Jet1) => p.1.1) p0 :=
    contDiffAt_fst.comp p0 contDiffAt_fst
  have hDB : ContDiffAt ℝ ∞ (fun p : (BG × DBSpace) × (Bilin × Jet1) => p.1.2) p0 :=
    contDiffAt_snd.comp p0 contDiffAt_fst
  apply contDiffAt_clm_of_apply
  intro v
  apply contDiffAt_clm_of_apply
  intro w
  simp only [lowerTerm_apply, lieFirst]
  exact (contDiffAt_const.mul (contDiffAt_ricciFirst hInv hG hJ v w)).add
    (((((hJ.clm_apply (contDiffAt_fieldValue hInv hG hJ hB)).clm_apply
      contDiffAt_const).clm_apply contDiffAt_const).add
      ((hG.clm_apply (contDiffAt_fieldFirst hInv hG hJ hB hDB v)).clm_apply
        contDiffAt_const)).add
      ((hG.clm_apply contDiffAt_const).clm_apply
        (contDiffAt_fieldFirst hInv hG hJ hB hDB w)))

end Poincare.DeTurckLowerJointSmoothness
