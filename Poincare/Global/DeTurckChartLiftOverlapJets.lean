import Poincare.Global.DeTurckChartLiftCoordinates
import Poincare.Global.DeTurckChartIndependentPullback
import Poincare.Global.DeTurckJetLinearizationDefinitions

/-!
# Actual chart-lift overlap jets

The true chart overlap gives C3 regularity for the actual transition and local
pullback equality for an arbitrary coefficient field. Local equality then gives
its value, first derivative, and second derivative equality, even without
regularity assumptions on that field.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open Filter Set
open scoped Manifold ContDiff Topology
universe u
namespace Poincare.DeTurckChartLiftOverlapJets
open DeTurckPrincipalSecondJet
local notation "𝓙" => Poincare.closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓙 ∞ M]

theorem overlap_open (a b : M) :
    IsOpen ((extChartAt 𝓙 a).symm ≫ extChartAt 𝓙 b).source := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hy' : y ∈ (extChartAt 𝓙 a).target ∧
      (extChartAt 𝓙 a).symm y ∈ (extChartAt 𝓙 b).source := by
    simpa only [PartialEquiv.trans_source, PartialEquiv.symm_source] using hy
  have htarget := (isOpen_extChartAt_target a).mem_nhds hy'.1
  have hpreimage := (continuousAt_extChartAt_symm'' hy'.1).preimage_mem_nhds
    ((isOpen_extChartAt_source b).mem_nhds hy'.2)
  simpa only [PartialEquiv.trans_source, PartialEquiv.symm_source] using
    inter_mem htarget hpreimage

theorem overlap_eventually (a b : M) {z : E}
    (hz : z ∈ (extChartAt 𝓙 a).target)
    (hy : (extChartAt 𝓙 a).symm z ∈ (extChartAt 𝓙 b).source) :
    ∀ᶠ y : E in nhds z, y ∈ (extChartAt 𝓙 a).target ∧
      (extChartAt 𝓙 a).symm y ∈ (extChartAt 𝓙 b).source := by
  have hz' : z ∈ ((extChartAt 𝓙 a).symm ≫ extChartAt 𝓙 b).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hz, hy⟩
  simpa only [PartialEquiv.trans_source, PartialEquiv.symm_source] using
    (overlap_open a b).mem_nhds hz'

theorem chartTransition_contDiffAt_three (a b : M) {z : E}
    (hz : z ∈ (extChartAt 𝓙 a).target)
    (hy : (extChartAt 𝓙 a).symm z ∈ (extChartAt 𝓙 b).source) :
    ContDiffAt ℝ 3 (Poincare.GeodesicTransport.chartTransition a b) z := by
  have hz' : z ∈ ((extChartAt 𝓙 a).symm ≫ extChartAt 𝓙 b).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hz, hy⟩
  have h := contDiffWithinAt_ext_coord_change (I := 𝓙) (n := 3) b a hz'
  have hAt : ContDiffAt ℝ 3 ((extChartAt 𝓙 b) ∘ (extChartAt 𝓙 a).symm) z := by
    simpa [ModelWithCorners.range_eq_univ] using h
  simpa [Poincare.GeodesicTransport.chartTransition] using hAt


theorem chartMetric_transport_eventually
    (H : ∀ x : M, TangentSpace 𝓙 x →L[ℝ] TangentSpace 𝓙 x →L[ℝ] ℝ)
    (a b : M) {z : E}
    (hz : z ∈ (extChartAt 𝓙 a).target)
    (hy : (extChartAt 𝓙 a).symm z ∈ (extChartAt 𝓙 b).source) :
    CovariantDerivative.chartMetric H a =ᶠ[nhds z]
      (fun y => Poincare.pullbackBilinearForm
        (CovariantDerivative.chartMetric H b (Poincare.GeodesicTransport.chartTransition a b y))
        (fderiv ℝ (Poincare.GeodesicTransport.chartTransition a b) y)) := by
  filter_upwards [overlap_eventually a b hz hy] with y hy'
  ext v w
  exact (Poincare.chartBilinearTensor_chartTransitionDeriv H a b hy'.1 hy'.2 v w).symm

theorem chartLift_transport_eventually
    (a b : M) (F : E → Bilin) {z : E}
    (hz : z ∈ (extChartAt 𝓙 a).target)
    (hy : (extChartAt 𝓙 a).symm z ∈ (extChartAt 𝓙 b).source) :
    CovariantDerivative.chartMetric (Poincare.DeTurckChartLift.chartLift b F) a =ᶠ[nhds z]
      (fun y => Poincare.pullbackBilinearForm
        (F (Poincare.GeodesicTransport.chartTransition a b y))
        (fderiv ℝ (Poincare.GeodesicTransport.chartTransition a b) y)) := by
  filter_upwards [overlap_eventually a b hz hy,
    chartMetric_transport_eventually (Poincare.DeTurckChartLift.chartLift b F) a b hz hy]
    with y hy' htransport
  rw [htransport]
  rw [Poincare.DeTurckChartLift.chartMetric_chartLift b F _]
  exact (extChartAt 𝓙 b).map_source hy'.2

/-- The actual transition and the whole chart-lift two-jet agree on true overlap. -/
theorem chartLift_overlap_twoJet :
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
(anchor₁ anchor₂ : M) (F : Poincare.DeTurckPrincipalSecondJet.E → Poincare.DeTurckPrincipalSecondJet.Bilin) (z : Poincare.DeTurckPrincipalSecondJet.E),
z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₁).target →
(extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₁).symm z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₂).source →
let phi := Poincare.GeodesicTransport.chartTransition anchor₁ anchor₂
let FA := _root_.CovariantDerivative.chartMetric (I := Poincare.closedSmoothModelWithCorners 3)
 (Poincare.DeTurckChartLift.chartLift anchor₂ F) anchor₁
let TF := fun y => Poincare.pullbackBilinearForm (F (phi y)) (fderiv ℝ phi y)
ContDiffAt ℝ 3 phi z ∧
Filter.Eventually (fun y => FA y = TF y) (nhds z) ∧
((FA z, fderiv ℝ FA z), fderiv ℝ (fderiv ℝ FA) z) =
 ((TF z, fderiv ℝ TF z), fderiv ℝ (fderiv ℝ TF) z) := by
  intro M _ _ _ _ anchor₁ anchor₂ F z hz hy
  dsimp only
  have hphi := chartTransition_contDiffAt_three anchor₁ anchor₂ hz hy
  have heq := chartLift_transport_eventually anchor₁ anchor₂ F hz hy
  refine ⟨hphi, heq, ?_⟩
  exact Prod.ext (Prod.ext heq.eq_of_nhds heq.fderiv_eq) heq.fderiv.fderiv_eq

end Poincare.DeTurckChartLiftOverlapJets
