import Poincare.Global.DeTurckActualEvolutionDerivative
import Poincare.Global.DeTurckActualSpatialCoefficients
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators
universe u

namespace Poincare.DeTurckDifferentialSymmetry
open DeTurckPrincipalSecondJet DeTurckJetLinearization

local instance differentialSymmetryCanonical1 : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedAddCommGroup
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ)

local instance differentialSymmetryCanonical2 : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedSpace
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance differentialSymmetryCanonical3 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance differentialSymmetryCanonical4 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance differentialSymmetryCanonical5 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance differentialSymmetryCanonical6 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance differentialSymmetryCanonical7 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ)

local instance differentialSymmetryCanonical8 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance differentialSymmetryCanonical9 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup

local instance differentialSymmetryCanonical10 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace

local instance differentialSymmetryCanonical11 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup

local instance differentialSymmetryCanonical12 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace

local instance differentialSymmetryCanonical13 : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid

/-- Every slice of actual geometric DeTurck evolution is tensor-symmetric. -/
private theorem actual_evolution_symmetric
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (s : ℝ) (z v w : E) :
    deTurckChartMetricEvolutionBilin gt bg anchor s z v w =
      deTurckChartMetricEvolutionBilin gt bg anchor s z w v := by
  have hRic : deTurckChartRicciBilin gt anchor s z v w =
      deTurckChartRicciBilin gt anchor s z w v := by
    apply CovariantDerivative.chartMetric_symm
    intro x a b
    simp only [ricciContinuousBilinAt_apply]
    exact (gt s).ricciAt_symm' x a b
  have hLie : deTurckChartLieBilin gt bg anchor s z v w =
      deTurckChartLieBilin gt bg anchor s z w v := by
    apply CovariantDerivative.chartMetric_symm
    intro x a b
    simp only [lieDerivMetricBilinAt_apply]
    exact lieDerivMetricAt_symm (gt s) (deTurckVectorField gt bg s) x a b
  simp only [deTurckChartMetricEvolutionBilin, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hRic, hLie]

/-- A symmetric coefficient germ gives a tensor-symmetric principal contraction. -/
private theorem principal_symmetric (G : Bilin) (q : E → Bilin) (z : E)
    (hs : ∀ᶠ y in nhds z, ∀ v w : E, q y v w = q y w v) (v w : E) :
    DeTurckJetLinearization.principal G (fderiv ℝ (fderiv ℝ q) z) v w =
      DeTurckJetLinearization.principal G (fderiv ℝ (fderiv ℝ q) z) w v := by
  simp only [DeTurckJetLinearization.principal, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [DeTurckJetRealization.germ_second_fiber_symmetric q z hs
    (basis3 i) (basis3 j) v w]

/-- The full differential and its combined actual lower action preserve
fiber symmetry at genuine metric jets. The inverse variation against the
initial metric Hessian remains in the zero-order action. -/
theorem differential_and_lower_symmetric :
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
(anchor : M) (q : Poincare.DeTurckPrincipalSecondJet.E → Poincare.DeTurckPrincipalSecondJet.Bilin) (z : Poincare.DeTurckPrincipalSecondJet.E),
z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor).target →
Filter.Eventually (fun y => Poincare.GeodesicTransport.cutoff (n := 3) anchor y = 1) (nhds z) →
ContDiffAt ℝ 2 q z →
Filter.Eventually (fun y => ∀ v w : Poincare.DeTurckPrincipalSecondJet.E, q y v w = q y w v) (nhds z) →
let G0 := _root_.CovariantDerivative.chartMetric (I := Poincare.closedSmoothModelWithCorners 3) g0.inner anchor
let B := Poincare.GeodesicTransport.chartChristoffelField bg anchor
let full := Poincare.DeTurckJetLinearization.differential (B z) (fderiv ℝ B z)
 (G0 z) (fderiv ℝ G0 z) (fderiv ℝ (fderiv ℝ G0) z)
 ((q z, fderiv ℝ q z), fderiv ℝ (fderiv ℝ q) z)
let lower := Poincare.DeTurckSpatialCoefficients.zeroOrder (B z) (fderiv ℝ B z)
 (G0 z) (fderiv ℝ G0 z) (fderiv ℝ (fderiv ℝ G0) z) (q z) +
 Poincare.DeTurckSpatialCoefficients.firstOrder (B z) (fderiv ℝ B z)
 (G0 z) (fderiv ℝ G0 z) (fderiv ℝ q z)
(∀ v w : Poincare.DeTurckPrincipalSecondJet.E, full v w = full w v) ∧
(∀ v w : Poincare.DeTurckPrincipalSecondJet.E, lower v w = lower w v) := by
  intro M _ _ _ _ g0 bg anchor q z hz hcut hq hsym
  dsimp only
  let G0 : E → Bilin := CovariantDerivative.chartMetric
    (I := closedSmoothModelWithCorners 3) g0.inner anchor
  let B := GeodesicTransport.chartChristoffelField bg anchor
  let full := differential (B z) (fderiv ℝ B z)
    (G0 z) (fderiv ℝ G0 z) (fderiv ℝ (fderiv ℝ G0) z)
    ((q z, fderiv ℝ q z), fderiv ℝ (fderiv ℝ q) z)
  let lower := DeTurckSpatialCoefficients.zeroOrder (B z) (fderiv ℝ B z)
      (G0 z) (fderiv ℝ G0 z) (fderiv ℝ (fderiv ℝ G0) z) (q z) +
    DeTurckSpatialCoefficients.firstOrder (B z) (fderiv ℝ B z)
      (G0 z) (fderiv ℝ G0 z) (fderiv ℝ q z)
  change (∀ v w : E, full v w = full w v) ∧
    (∀ v w : E, lower v w = lower w v)
  obtain ⟨η, _, _, _, _, hF, hcF, hsupport, hsF, hj0, hj1, hj2⟩ :=
    DeTurckJetRealization.exists_compact_symmetric_realization q z
      (extChartAt (closedSmoothModelWithCorners 3) anchor).target
      (isOpen_extChartAt_target anchor) hz hq hsym
  let F : E → Bilin := DeTurckJetRealization.realized η q z
  let H := DeTurckChartLift.chartLift anchor F
  obtain ⟨ε, hε, gt, _, hinner, _⟩ :=
    DeTurckChartLift.exists_actual_metric_variation
      M g0 anchor F hF hcF hsupport hsF
  have hH : ContMDiff (closedSmoothModelWithCorners 3)
      ((closedSmoothModelWithCorners 3).prod 𝓘(ℝ, Bilin)) ∞
      (fun x : M => TotalSpace.mk' Bilin x (H x)) :=
    DeTurckChartLift.chartLift_contMDiff M anchor F hF hcF hsupport
  have hparameter : ∀ᶠ s : ℝ in nhds 0, |s| < ε := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro s hs
    simpa only [Real.dist_eq, sub_zero] using hs
  have hAffine : ∀ᶠ s : ℝ in nhds 0, ∀ x : M,
      (gt s).inner x = g0.inner x + s • H x := by
    filter_upwards [hparameter] with s hs
    exact hinner s hs
  let Fc : E → Bilin := CovariantDerivative.chartMetric
    (I := closedSmoothModelWithCorners 3) H anchor
  have hrecover : Fc =ᶠ[nhds z] F := by
    filter_upwards [(isOpen_extChartAt_target anchor).mem_nhds hz] with y hy
    exact DeTurckChartLift.chartMetric_chartLift anchor F y hy
  have hc0 : Fc z = q z := hrecover.self_of_nhds.trans hj0
  have hc1 : fderiv ℝ Fc z = fderiv ℝ q z := hrecover.fderiv_eq.trans hj1
  have hc2 : fderiv ℝ (fderiv ℝ Fc) z = fderiv ℝ (fderiv ℝ q) z :=
    (hrecover.fderiv (𝕜 := ℝ)).fderiv_eq.trans hj2
  have hder : HasDerivAt
      (fun s => deTurckChartMetricEvolutionBilin gt bg anchor s z) full 0 := by
    have hd := DeTurckActualEvolutionDerivative.hasDerivAt_chartEvolution_of_affine_inner
      M g0 bg gt H hH hAffine anchor z hz hcut
    change HasDerivAt _
      (differential (B z) (fderiv ℝ B z)
        (G0 z) (fderiv ℝ G0 z) (fderiv ℝ (fderiv ℝ G0) z)
        ((Fc z, fderiv ℝ Fc z), fderiv ℝ (fderiv ℝ Fc) z)) 0 at hd
    rw [hc0, hc1, hc2] at hd
    exact hd
  have hfull : ∀ v w : E, full v w = full w v := by
    intro v w
    have hvw := (hder.clm_apply (hasDerivAt_const 0 v)).clm_apply
      (hasDerivAt_const 0 w)
    have hwv := (hder.clm_apply (hasDerivAt_const 0 w)).clm_apply
      (hasDerivAt_const 0 v)
    have heq : (fun s => deTurckChartMetricEvolutionBilin gt bg anchor s z v w)
        =ᶠ[nhds 0]
        (fun s => deTurckChartMetricEvolutionBilin gt bg anchor s z w v) :=
      Filter.Eventually.of_forall (fun s => actual_evolution_symmetric gt bg anchor s z v w)
    simpa only [map_zero, add_zero] using hvw.unique (hwv.congr_of_eventuallyEq heq)
  refine ⟨hfull, ?_⟩
  intro v w
  have hdecomp := (DeTurckActualSpatialCoefficients.actual_spatial_coefficients
    M g0 bg anchor).2.2.2.2.2 z ⟨hz, hcut⟩
      ((q z, fderiv ℝ q z), fderiv ℝ (fderiv ℝ q) z)
  have hwhole : full = DeTurckJetLinearization.principal (G0 z) (fderiv ℝ (fderiv ℝ q) z) + lower := by
    simpa only [full, lower, add_assoc] using hdecomp
  have hvw := congrArg (fun A : Bilin => A v w) hwhole
  have hwv := congrArg (fun A : Bilin => A w v) hwhole
  simp only [ContinuousLinearMap.add_apply] at hvw hwv
  have hp := principal_symmetric (G0 z) q z hsym v w
  linarith only [hvw, hwv, hp, hfull v w]

end Poincare.DeTurckDifferentialSymmetry
