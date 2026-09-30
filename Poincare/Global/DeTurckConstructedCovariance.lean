import Poincare.Global.DeTurckActualEvolutionDerivative
import Poincare.Global.DeTurckBUCChartCovariance
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Topology
universe u

namespace Poincare.DeTurckConstructedCovariance
open DeTurckPrincipalSecondJet

local instance constructedCovarianceCanonical1 : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedAddCommGroup
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ)

local instance constructedCovarianceCanonical2 : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedSpace
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance constructedCovarianceCanonical3 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance constructedCovarianceCanonical4 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance constructedCovarianceCanonical5 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance constructedCovarianceCanonical6 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance constructedCovarianceCanonical7 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ)

local instance constructedCovarianceCanonical8 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance constructedCovarianceCanonical9 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup

local instance constructedCovarianceCanonical10 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace

local instance constructedCovarianceCanonical11 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup

local instance constructedCovarianceCanonical12 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace

local instance constructedCovarianceCanonical13 : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid

/-- Full linearized covariance along the constructed compact metric variation. -/
theorem chartLift_differential_covariance :
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
(g0 bg : Poincare.ClosedSmoothRiemannianMetric 3 M) (liftAnchor : M)
(F : Poincare.DeTurckPrincipalSecondJet.E → Poincare.DeTurckPrincipalSecondJet.Bilin),
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F → HasCompactSupport F →
tsupport F ⊆ (extChartAt (Poincare.closedSmoothModelWithCorners 3) liftAnchor).target →
(∀ z v w : Poincare.DeTurckPrincipalSecondJet.E, F z v w = F z w v) →
let H := Poincare.DeTurckChartLift.chartLift liftAnchor F
let DQ := fun (anchor : M) (y : Poincare.DeTurckPrincipalSecondJet.E) =>
 let G0 := _root_.CovariantDerivative.chartMetric
  (I := Poincare.closedSmoothModelWithCorners 3) g0.inner anchor
 let DG0 := fderiv ℝ G0
 let D2G0 := fderiv ℝ DG0
 let F_a := _root_.CovariantDerivative.chartMetric
  (I := Poincare.closedSmoothModelWithCorners 3) H anchor
 let DF_a := fderiv ℝ F_a
 let D2F_a := fderiv ℝ DF_a
 let B := Poincare.GeodesicTransport.chartChristoffelField bg anchor
 let DB := fderiv ℝ B
 Poincare.DeTurckJetLinearization.differential
  (B y) (DB y) (G0 y) (DG0 y) (D2G0 y)
  ((F_a y, DF_a y), D2F_a y)
∀ (anchor₁ anchor₂ : M) (z : Poincare.DeTurckPrincipalSecondJet.E),
z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₁).target →
(extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₁).symm z ∈
 (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₂).source →
Filter.Eventually
 (fun y => Poincare.GeodesicTransport.cutoff (n := 3) anchor₁ y = 1) (nhds z) →
Filter.Eventually
 (fun y => Poincare.GeodesicTransport.cutoff (n := 3) anchor₂ y = 1)
 (nhds (Poincare.GeodesicTransport.chartTransition anchor₁ anchor₂ z)) →
Poincare.pullbackBilinearForm
 (DQ anchor₂ (Poincare.GeodesicTransport.chartTransition anchor₁ anchor₂ z))
 (Poincare.GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z) =
DQ anchor₁ z := by
  intro M _ _ _ _ g0 bg liftAnchor F hF hcompact hsupport hsymm
  dsimp only
  intro anchor₁ anchor₂ z hz hy hcut₁ hcut₂
  let H := DeTurckChartLift.chartLift liftAnchor F
  let DQ := fun (anchor : M) (y : E) =>
    let G0 := CovariantDerivative.chartMetric
      (I := closedSmoothModelWithCorners 3) g0.inner anchor
    let F_a := CovariantDerivative.chartMetric
      (I := closedSmoothModelWithCorners 3) H anchor
    let B := GeodesicTransport.chartChristoffelField bg anchor
    DeTurckJetLinearization.differential
      (B y) (fderiv ℝ B y) (G0 y) (fderiv ℝ G0 y)
      (fderiv ℝ (fderiv ℝ G0) y)
      ((F_a y, fderiv ℝ F_a y), fderiv ℝ (fderiv ℝ F_a) y)
  let z₂ := GeodesicTransport.chartTransition anchor₁ anchor₂ z
  let T := GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z
  change pullbackBilinearForm (DQ anchor₂ z₂) T = DQ anchor₁ z
  obtain ⟨ε, hε, gt, hgt0, hinner, hchart⟩ :=
    DeTurckChartLift.exists_actual_metric_variation
      M g0 liftAnchor F hF hcompact hsupport hsymm
  have hH : ContMDiff (closedSmoothModelWithCorners 3)
      ((closedSmoothModelWithCorners 3).prod 𝓘(ℝ, Bilin)) ∞
      (fun x : M => TotalSpace.mk' Bilin x (H x)) :=
    DeTurckChartLift.chartLift_contMDiff
      M liftAnchor F hF hcompact hsupport
  have hparameter : ∀ᶠ s : ℝ in nhds 0, |s| < ε := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro s hs
    simpa only [Real.dist_eq, sub_zero] using hs
  have hAffine : ∀ᶠ s : ℝ in nhds 0, ∀ x : M,
      (gt s).inner x = g0.inner x + s • H x := by
    filter_upwards [hparameter] with s hs
    exact hinner s hs
  have hz₂ : z₂ ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor₂).target :=
    (extChartAt (closedSmoothModelWithCorners 3) anchor₂).map_source hy
  have h₁ : HasDerivAt
      (fun s => deTurckChartMetricEvolutionBilin gt bg anchor₁ s z)
      (DQ anchor₁ z) 0 :=
    DeTurckActualEvolutionDerivative.hasDerivAt_chartEvolution_of_affine_inner
      M g0 bg gt H hH hAffine anchor₁ z hz hcut₁
  have h₂ : HasDerivAt
      (fun s => deTurckChartMetricEvolutionBilin gt bg anchor₂ s z₂)
      (DQ anchor₂ z₂) 0 :=
    DeTurckActualEvolutionDerivative.hasDerivAt_chartEvolution_of_affine_inner
      M g0 bg gt H hH hAffine anchor₂ z₂ hz₂ hcut₂
  ext v w
  change DQ anchor₂ z₂ (T v) (T w) = DQ anchor₁ z v w
  have hleft := (h₂.clm_apply (hasDerivAt_const 0 (T v))).clm_apply
    (hasDerivAt_const 0 (T w))
  have hright := (h₁.clm_apply (hasDerivAt_const 0 v)).clm_apply
    (hasDerivAt_const 0 w)
  have hcov : (fun s => deTurckChartMetricEvolutionBilin gt bg anchor₂ s z₂
      (T v) (T w)) =ᶠ[nhds 0]
      (fun s => deTurckChartMetricEvolutionBilin gt bg anchor₁ s z v w) :=
    Filter.Eventually.of_forall (fun s =>
      deTurckChartMetricEvolutionBilin_chartTransitionDeriv
        gt bg s anchor₁ anchor₂ hz hy v w)
  simpa only [map_zero, add_zero] using
    hleft.unique (hright.congr_of_eventuallyEq hcov)

end Poincare.DeTurckConstructedCovariance
