import Poincare.Global.DeTurckJetLinearizationDefinitions
import Poincare.Global.DeTurckInverseEntryDerivative
import Poincare.Global.DeTurckLowerJointSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section
open scoped ContDiff BigOperators

namespace Poincare.DeTurckJetLinearization
open DeTurckPrincipalSecondJet

local instance : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedAddCommGroup
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ)

local instance : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedSpace
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ)

local instance : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup

local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace

local instance : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup

local instance : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace

local instance : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid

private theorem hasFDerivAt_clm_of_apply
    {D V W : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : D → V →L[ℝ] W} {f' : D →L[ℝ] V →L[ℝ] W} {x : D}
    (h : ∀ v, HasFDerivAt (fun y => f y v)
      ((ContinuousLinearMap.apply ℝ W v).comp f') x) :
    HasFDerivAt f f' x := by
  let d := Module.finrank ℝ V
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : W ≃L[ℝ] W)).trans (ContinuousLinearEquiv.piRing (Fin d))
  apply (e₂.comp_hasFDerivAt_iff).mp
  apply hasFDerivAt_pi''
  intro i
  change HasFDerivAt (fun y => f y (e₁.symm (Pi.single i 1)))
    ((ContinuousLinearMap.apply ℝ W (e₁.symm (Pi.single i 1))).comp f') x
  exact h _

/-- The full derivative of the actual DeTurck jet evolution, retaining inverse
variation against the initial second jet for the Hamilton linear operator. -/
theorem hasFDerivAt_evolution :
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
    letI : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ);
    letI : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
    letI : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup;
    letI : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace;
    letI : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup;
    letI : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace;
    letI : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid;
    ∀ (B : Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)
    (DB : Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)
    (G0 : Poincare.DeTurckPrincipalSecondJet.Bilin) (J0 : Poincare.DeTurckPrincipalSecondJet.Jet1) (H0 : Poincare.DeTurckJetLinearization.Jet2), G0.IsInvertible →
    HasFDerivAt (Poincare.DeTurckJetLinearization.evolution B DB) (Poincare.DeTurckJetLinearization.differential B DB G0 J0 H0) ((G0,J0),H0) ∧
    ∀ (h : Poincare.DeTurckJetLinearization.Variables) (v w : Poincare.DeTurckPrincipalSecondJet.E), (Poincare.DeTurckJetLinearization.differential B DB G0 J0 H0 h) v w =
     (∑ i : Fin 3, ∑ j : Fin 3, Poincare.DeTurckPrincipalSecondJet.inverseEntries G0 i j * h.2 (Poincare.DeTurckPrincipalSecondJet.basis3 i) (Poincare.DeTurckPrincipalSecondJet.basis3 j) v w) +
     (∑ i : Fin 3, ∑ j : Fin 3,
       (-(∑ k : Fin 3, ∑ l : Fin 3,
         Poincare.DeTurckPrincipalSecondJet.inverseEntries G0 i k * h.1.1 (Poincare.DeTurckPrincipalSecondJet.basis3 k) (Poincare.DeTurckPrincipalSecondJet.basis3 l) * Poincare.DeTurckPrincipalSecondJet.inverseEntries G0 l j)) * H0 (Poincare.DeTurckPrincipalSecondJet.basis3 i) (Poincare.DeTurckPrincipalSecondJet.basis3 j) v w) +
     Poincare.DeTurckJetLinearization.lowerDifferential B DB G0 J0 h.1 v w := by
  intro B DB G0 J0 H0 hG0
  constructor
  · have hLower := (DeTurckLowerJetSmoothness.contDiffAt_lowerTerm B DB G0 J0 hG0).differentiableAt (by simp)
    have hL := hLower.hasFDerivAt.comp ((G0, J0), H0)
      (ContinuousLinearMap.fst ℝ (Bilin × Jet1) Jet2).hasFDerivAt
    have hInv (i j : Fin 3) :
        HasFDerivAt (fun p : Variables => inverseEntries p.1.1 i j)
          ((DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j).comp
            metricProjection) ((G0, J0), H0) := by
      have hP : HasFDerivAt (fun p : Variables => p.1.1)
          metricProjection ((G0, J0), H0) :=
        metricProjection.hasFDerivAt (x := ((G0, J0), H0))
      have hA : HasFDerivAt (fun G : Bilin => inverseEntries G i j)
          (DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j) G0 :=
        DeTurckInverseEntryDerivative.hasFDerivAt_inverseEntry G0 i j hG0
      exact HasFDerivAt.comp (𝕜 := ℝ) (E := Variables) (F := Bilin) (G := ℝ)
        (f := fun p : Variables => p.1.1) (f' := metricProjection)
        (g := fun G : Bilin => inverseEntries G i j)
        (g' := DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j)
        ((G0, J0), H0) hA hP
    have hTerm (i j : Fin 3) :
        HasFDerivAt (fun p : Variables =>
          inverseEntries p.1.1 i j • p.2 (basis3 i) (basis3 j))
          (inverseEntries G0 i j • secondJetEvaluation i j +
            ((DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j).comp
              metricProjection).smulRight (H0 (basis3 i) (basis3 j)))
          ((G0, J0), H0) := by
      apply hasFDerivAt_clm_of_apply
      intro v
      apply hasFDerivAt_clm_of_apply
      intro w
      let e : Variables →L[ℝ] ℝ :=
        (ContinuousLinearMap.apply ℝ ℝ w).comp
          ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).comp
            (secondJetEvaluation i j))
      have he : HasFDerivAt (fun p : Variables => p.2 (basis3 i) (basis3 j) v w)
          e ((G0, J0), H0) := e.hasFDerivAt
      convert (hInv i j).mul he using 1
      apply ContinuousLinearMap.ext
      intro h
      simp only [e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.apply_apply, smul_eq_mul]
      ring
    have hPrincipal : HasFDerivAt (fun p : Variables => principal p.1.1 p.2)
        (∑ i : Fin 3, ∑ j : Fin 3,
          (inverseEntries G0 i j • secondJetEvaluation i j +
            ((DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j).comp
              metricProjection).smulRight (H0 (basis3 i) (basis3 j))))
        ((G0, J0), H0) := by
      unfold principal
      apply HasFDerivAt.fun_sum (𝕜 := ℝ) (E := Variables) (F := Bilin)
      intro i _
      apply HasFDerivAt.fun_sum (𝕜 := ℝ) (E := Variables) (F := Bilin)
      intro j _
      exact hTerm i j
    convert hPrincipal.add hL using 1
    apply ContinuousLinearMap.ext
    intro h
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [differential, lowerDifferential, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst', metricProjection, secondJetEvaluation,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.apply_apply,
      smul_eq_mul, Finset.sum_add_distrib]
    ring
  · intro h v w
    have hInv (i j : Fin 3) :
        DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j h.1.1 =
          -(∑ k : Fin 3, ∑ l : Fin 3,
            inverseEntries G0 i k * h.1.1 (basis3 k) (basis3 l) * inverseEntries G0 l j) := by
      simp only [DeTurckInverseEntryDerivative.inverseEntryDerivative,
        DeTurckInverseEntryDerivative.entryCLM,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.apply_apply, smul_eq_mul]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    simp only [differential, metricProjection, secondJetEvaluation,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      hInv, smul_eq_mul]
    abel

end Poincare.DeTurckJetLinearization
