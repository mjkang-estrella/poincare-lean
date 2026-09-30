import Poincare.Global.DeTurckParameterJet
import Poincare.Global.DeTurckJetLinearization
import Poincare.Global.DeTurckMetricVariation
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators
universe u

namespace Poincare.DeTurckActualEvolutionDerivative
open DeTurckPrincipalSecondJet DeTurckPrincipalIdentity

local instance actualEvolutionCanonical1 : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedAddCommGroup
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ)

local instance actualEvolutionCanonical2 : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedSpace
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance actualEvolutionCanonical3 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance actualEvolutionCanonical4 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance actualEvolutionCanonical5 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance actualEvolutionCanonical6 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance actualEvolutionCanonical7 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ)

local instance actualEvolutionCanonical8 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance actualEvolutionCanonical9 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup

local instance actualEvolutionCanonical10 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace

local instance actualEvolutionCanonical11 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup

local instance actualEvolutionCanonical12 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace

local instance actualEvolutionCanonical13 : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid

/-- The explicit full finite-jet expression is the actual geometric chart evolution. -/
private theorem evolution_eq_actual
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (g bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1) :
    let G := CovariantDerivative.chartMetric g.inner anchor
    let B := GeodesicTransport.chartChristoffelField bg anchor
    DeTurckJetLinearization.evolution (B z) (fderiv ℝ B z)
      ((G z, fderiv ℝ G z), fderiv ℝ (fderiv ℝ G) z) =
      deTurckChartMetricEvolutionBilin (fun _ => g) bg anchor 0 z := by
  dsimp only
  ext v w
  have hR := ricci_eq_secondJet_add_first g anchor z hz hcut v w
  have hL := lie_eq_secondJet_add_first g bg anchor z hz hcut v w
  have hcancel := chartMetric_secondJet_cancellation g anchor z hz v w
  rw [evolution_eq_coordinate_expression g bg anchor z hz hcut v w]
  simp only [DeTurckJetLinearization.evolution, DeTurckJetLinearization.principal,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, lowerTerm_apply]
  dsimp only [spatialPrincipal] at hcancel
  linarith only [hR, hL, hcancel]

/-- Smooth bundle sections have smooth unblended coefficients on the true target. -/
private theorem chartMetric_contDiffOn
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (H : ∀ x : M, TangentSpace (closedSmoothModelWithCorners 3) x →L[ℝ]
      TangentSpace (closedSmoothModelWithCorners 3) x →L[ℝ] ℝ)
    (hH : ContMDiff (closedSmoothModelWithCorners 3)
      ((closedSmoothModelWithCorners 3).prod 𝓘(ℝ, Bilin)) ∞
      (fun x : M => TotalSpace.mk' Bilin x (H x))) (anchor : M) :
    ContDiffOn ℝ 2 (CovariantDerivative.chartMetric H anchor)
      (extChartAt (closedSmoothModelWithCorners 3) anchor).target := by
  have htop : ContDiffOn ℝ ∞ (CovariantDerivative.chartMetric H anchor)
      (extChartAt (closedSmoothModelWithCorners 3) anchor).target := by
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    exact (CovariantDerivative.contMDiffOn_chartMetric_pairing
      (I := closedSmoothModelWithCorners 3) H anchor
      (m := ∞) (by simp) hH v w).contDiffOn
  exact htop.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- The derivative of actual geometric evolution along a common affine inner variation. -/
theorem hasDerivAt_chartEvolution_of_affine_inner :
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
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
[ChartedSpace Poincare.DeTurckPrincipalSecondJet.E M]
[IsManifold (Poincare.closedSmoothModelWithCorners 3) ((⊤ : ENat) : WithTop ENat) M]
(g0 bg : Poincare.ClosedSmoothRiemannianMetric 3 M)
(gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
(H : ∀ x : M,
 TangentSpace (Poincare.closedSmoothModelWithCorners 3) x →L[ℝ]
 TangentSpace (Poincare.closedSmoothModelWithCorners 3) x →L[ℝ] ℝ),
ContMDiff (Poincare.closedSmoothModelWithCorners 3)
 ((Poincare.closedSmoothModelWithCorners 3).prod
  𝓘(ℝ, Poincare.DeTurckPrincipalSecondJet.Bilin))
 ((⊤ : ENat) : WithTop ENat)
 (fun x : M => Bundle.TotalSpace.mk' Poincare.DeTurckPrincipalSecondJet.Bilin x (H x)) →
Filter.Eventually (fun s : ℝ => ∀ x : M,
 (gt s).inner x = g0.inner x + s • H x) (nhds (0 : ℝ)) →
∀ (anchor : M) (z : Poincare.DeTurckPrincipalSecondJet.E),
z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor).target →
Filter.Eventually (fun y => Poincare.GeodesicTransport.cutoff (n := 3) anchor y = 1)
 (nhds z) →
let G0 := _root_.CovariantDerivative.chartMetric
 (I := Poincare.closedSmoothModelWithCorners 3) g0.inner anchor
let DG0 := fderiv ℝ G0
let D2G0 := fderiv ℝ DG0
let F := _root_.CovariantDerivative.chartMetric
 (I := Poincare.closedSmoothModelWithCorners 3) H anchor
let DF := fderiv ℝ F
let D2F := fderiv ℝ DF
let B := Poincare.GeodesicTransport.chartChristoffelField bg anchor
let DB := fderiv ℝ B
HasDerivAt
 (fun s => Poincare.deTurckChartMetricEvolutionBilin gt bg anchor s z)
 (Poincare.DeTurckJetLinearization.differential
  (B z) (DB z) (G0 z) (DG0 z) (D2G0 z)
  ((F z, DF z), D2F z)) 0 := by
  intro M _ _ _ _ g0 bg gt H hH hAffine anchor z hz hcut
  dsimp only
  let G : ℝ → E → Bilin := fun s => CovariantDerivative.chartMetric (gt s).inner anchor
  let G0 : E → Bilin := CovariantDerivative.chartMetric g0.inner anchor
  let F : E → Bilin := CovariantDerivative.chartMetric H anchor
  let B := GeodesicTransport.chartChristoffelField bg anchor
  let V := (extChartAt (closedSmoothModelWithCorners 3) anchor).target
  have hV : IsOpen V := isOpen_extChartAt_target anchor
  have hG0 : ContDiffOn ℝ 2 G0 V :=
    chartMetric_contDiffOn g0.inner g0.contMDiff_inner anchor
  have hF : ContDiffOn ℝ 2 F V := chartMetric_contDiffOn H hH anchor
  obtain ⟨ε, hε, hparameter⟩ := Metric.eventually_nhds_iff.mp hAffine
  have hinner (s : ℝ) (hs : |s| < ε) (x : M) :
      (gt s).inner x = g0.inner x + s • H x :=
    hparameter (by simpa only [Real.dist_eq, sub_zero] using hs) x
  have hcoeff (s : ℝ) (hs : |s| < ε) (y : E) : G s y = G0 y + s • F y := by
    ext v w
    rw [CovariantDerivative.chartMetric_apply, hinner s hs]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rfl
  have hGzero : G 0 = G0 := by
    funext y
    simpa only [zero_smul, add_zero] using hcoeff 0 (by simpa using hε) y
  have hjet : HasDerivAt
      (fun s => ((G s z, fderiv ℝ (G s) z), fderiv ℝ (fderiv ℝ (G s)) z))
      ((F z, fderiv ℝ F z), fderiv ℝ (fderiv ℝ F) z) 0 :=
    DeTurckParameterJet.twoJet_hasDerivAt_of_affine_on_open
      E Bilin V hV z hz ε hε G G0 F hG0 hF (fun s hs y _ => hcoeff s hs y)
  have hfinite := (DeTurckJetLinearization.hasFDerivAt_evolution
    (B z) (fderiv ℝ B z) (G0 z) (fderiv ℝ G0 z)
    (fderiv ℝ (fderiv ℝ G0) z)
    (chartMetric_isInvertible_of_cutoff g0 anchor z hcut)).1
  have hcurve : HasDerivAt
      (fun s => DeTurckJetLinearization.evolution (B z) (fderiv ℝ B z)
        ((G s z, fderiv ℝ (G s) z), fderiv ℝ (fderiv ℝ (G s)) z))
      (DeTurckJetLinearization.differential (B z) (fderiv ℝ B z)
        (G0 z) (fderiv ℝ G0 z) (fderiv ℝ (fderiv ℝ G0) z)
        ((F z, fderiv ℝ F z), fderiv ℝ (fderiv ℝ F) z)) 0 := by
    apply hfinite.comp_hasDerivAt_of_eq 0 hjet
    simp only [hGzero]
  refine hcurve.congr_of_eventuallyEq (𝕜 := ℝ) (F := Bilin) ?_
  exact Filter.Eventually.of_forall (fun s => by
    change deTurckChartMetricEvolutionBilin gt bg anchor s z =
      DeTurckJetLinearization.evolution (B z) (fderiv ℝ B z)
        ((G s z, fderiv ℝ (G s) z), fderiv ℝ (fderiv ℝ (G s)) z)
    rw [evolution_eq_actual (gt s) bg anchor z hz hcut]
    rfl)

end Poincare.DeTurckActualEvolutionDerivative
