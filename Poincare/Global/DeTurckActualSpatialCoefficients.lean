import Poincare.Global.DeTurckSpatialCoefficientDefinitions
import Poincare.Global.DeTurckPartialCoefficientSmoothness
import Poincare.Global.DeTurckInverseEntrySmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100
open scoped Manifold ContDiff Topology BigOperators
open Set Filter

universe u
namespace Poincare.DeTurckActualSpatialCoefficients
open DeTurckPrincipalSecondJet DeTurckJetLinearization DeTurckCoefficients

/-- Actual spatial coefficients of the full DeTurck linearization. The
metric and background jets are constructed from the given smooth metrics,
and the zero-order coefficient retains the inverse variation against D2g0.
These fields feed compact coefficient bounds and the genuine global linear
operator on the route to universal Hamilton input existence. -/
theorem actual_spatial_coefficients :
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
letI : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Bilin) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Bilin) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
letI : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Jet1 →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Jet1) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Jet1 →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Jet1) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
[ChartedSpace (Poincare.DeTurckPrincipalSecondJet.E) M]
[IsManifold (Poincare.closedSmoothModelWithCorners 3) ((⊤ : ENat) : WithTop ENat) M]
(g0 bg : Poincare.ClosedSmoothRiemannianMetric 3 M) (anchor : M),
let G0 := _root_.CovariantDerivative.chartMetric (I := Poincare.closedSmoothModelWithCorners 3) g0.inner anchor
let B := Poincare.GeodesicTransport.chartChristoffelField bg anchor
let U := (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor).target ∩
 (fun z : Poincare.DeTurckPrincipalSecondJet.E => Filter.Eventually (fun y => Poincare.GeodesicTransport.cutoff (n := 3) anchor y = 1) (nhds z))
IsOpen U ∧ (∀ z ∈ U, (G0 z).IsInvertible) ∧
(∀ i j : Fin 3, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun z => Poincare.DeTurckPrincipalSecondJet.inverseEntries (G0 z) i j) U) ∧
ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun z => Poincare.DeTurckSpatialCoefficients.zeroOrder (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z) (fderiv ℝ (fderiv ℝ G0) z)) U ∧
ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun z => Poincare.DeTurckSpatialCoefficients.firstOrder (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z)) U ∧
∀ z ∈ U,
let Gz : Poincare.DeTurckPrincipalSecondJet.Bilin := G0 z
let Jz : Poincare.DeTurckPrincipalSecondJet.Jet1 := fderiv ℝ G0 z
let Hz : Poincare.DeTurckJetLinearization.Jet2 := fderiv ℝ (fderiv ℝ G0) z
let Bz : Poincare.DeTurckCoefficients.Background := B z
let DBz : Poincare.DeTurckCoefficients.BackgroundDerivative := fderiv ℝ B z
∀ h : Poincare.DeTurckJetLinearization.Variables,

Poincare.DeTurckJetLinearization.differential Bz DBz Gz Jz
 Hz h =
Poincare.DeTurckJetLinearization.principal Gz h.2 + Poincare.DeTurckSpatialCoefficients.zeroOrder Bz DBz Gz Jz Hz h.1.1 + Poincare.DeTurckSpatialCoefficients.firstOrder Bz DBz Gz Jz h.1.2 := by
  intro M _ _ _ _ g0 bg anchor
  dsimp only
  let G0 : E → Bilin := CovariantDerivative.chartMetric
    (I := closedSmoothModelWithCorners 3) g0.inner anchor
  let B : E → Background := GeodesicTransport.chartChristoffelField bg anchor
  let target := (extChartAt (closedSmoothModelWithCorners 3) anchor).target
  let U : Set E := target ∩ {z | ∀ᶠ y in nhds z,
    GeodesicTransport.cutoff (n := 3) anchor y = 1}
  have htarget : IsOpen target := isOpen_extChartAt_target anchor
  have hU : IsOpen U := htarget.inter isOpen_setOf_eventually_nhds
  have hsub : U ⊆ target := fun _ hz => hz.1
  have hG : ContDiffOn ℝ ∞ G0 target := by
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    exact (CovariantDerivative.contMDiffOn_chartMetric_pairing
      (I := closedSmoothModelWithCorners 3) g0.inner anchor
      (m := ∞) (by simp) g0.contMDiff_inner v w).contDiffOn
  have hJ : ContDiffOn ℝ ∞ (fderiv ℝ G0) target :=
    hG.fderiv_of_isOpen htarget (by simp)
  have hH : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ G0)) target :=
    hJ.fderiv_of_isOpen htarget (by simp)
  have hB : ContDiff ℝ ∞ B :=
    GeodesicTransport.chartChristoffelField_contDiff_top bg anchor
  have hDB : ContDiff ℝ ∞ (fderiv ℝ B) := hB.fderiv_right (by simp)
  have hInv : ∀ z ∈ U, (G0 z).IsInvertible := by
    intro z hz
    exact DeTurckPrincipalIdentity.chartMetric_isInvertible_of_cutoff
      g0 anchor z hz.2
  have ha (i j : Fin 3) : ContDiffOn ℝ ∞
      (fun z => inverseEntries (G0 z) i j) U := by
    intro z hz
    exact (DeTurckInverseEntrySmoothness.contDiffAt_inverseEntry
      (G0 z) i j (hInv z hz)).comp_contDiffWithinAt z ((hG.mono hsub) z hz)
  have hpartial : ContDiffOn ℝ ∞
      (fun z => lowerDifferential (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z)) U := by
    intro z hz
    exact (DeTurckPartialCoefficientSmoothness.contDiffAt_partialLower
      (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z) (hInv z hz)).comp_contDiffWithinAt z
        (((hB.contDiffOn z hz).prodMk (hDB.contDiffOn z hz)).prodMk
          (((hG.mono hsub) z hz).prodMk ((hJ.mono hsub) z hz)))
  have hfirst : ContDiffOn ℝ ∞
      (fun z => DeTurckSpatialCoefficients.firstOrder
        (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z)) U :=
    hpartial.clm_comp contDiffOn_const
  have hzero : ContDiffOn ℝ ∞
      (fun z => DeTurckSpatialCoefficients.zeroOrder
        (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z)
        (fderiv ℝ (fderiv ℝ G0) z)) U := by
    apply contDiffOn_clm_apply.mpr
    intro h
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    simp only [DeTurckSpatialCoefficients.zeroOrder,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    apply ContDiffOn.add
    · apply ContDiffOn.sum
      intro i _
      apply ContDiffOn.sum
      intro j _
      apply ContDiffOn.mul
      · simp only [DeTurckInverseEntryDerivative.inverseEntryDerivative,
          ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        apply ContDiffOn.neg
        apply ContDiffOn.sum
        intro k _
        apply ContDiffOn.sum
        intro l _
        exact ((ha i k).mul (ha l j)).mul contDiffOn_const
      · exact (((((hH.mono hsub).clm_apply contDiffOn_const).clm_apply
          contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const)
    · exact (((hpartial.clm_apply contDiffOn_const).clm_apply
        contDiffOn_const).clm_apply contDiffOn_const)
  refine ⟨hU, hInv, ha, hzero, hfirst, ?_⟩
  intro z hz h
  simp only [differential, DeTurckJetLinearization.principal, DeTurckSpatialCoefficients.zeroOrder,
    DeTurckSpatialCoefficients.firstOrder, metricProjection, secondJetEvaluation,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.apply_apply]
  have hl : lowerDifferential (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z) h.1 =
      lowerDifferential (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z) (h.1.1, 0) +
      lowerDifferential (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z) (0, h.1.2) := by
    simpa using (lowerDifferential (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z)).map_add
      (h.1.1, 0) (0, h.1.2)
  rw [hl]
  abel

end Poincare.DeTurckActualSpatialCoefficients
