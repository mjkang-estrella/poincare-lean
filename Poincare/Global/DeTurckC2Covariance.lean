import Poincare.Global.DeTurckConstructedCovariance
import Poincare.Global.DeTurckChartLiftOverlapJets
import Poincare.Global.DeTurckPullbackTwoJet

/-!
# Full DeTurck differential covariance for symmetric C2 germs

A compact smooth symmetric realization supplies exactly the original two-jet.
The constructed metric variation proves full differential covariance for its
lift. Actual chart neighborhoods and matched pullback two-jets then transfer
that equality to the original coefficient germ.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology
universe u

namespace Poincare.DeTurckC2Covariance
open DeTurckPrincipalSecondJet

local instance c2CovarianceCanonical1 : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedAddCommGroup
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ)

local instance c2CovarianceCanonical2 : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
      ContinuousLinearMap.toNormedSpace
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
        (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance c2CovarianceCanonical3 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance c2CovarianceCanonical4 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance c2CovarianceCanonical5 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)

local instance c2CovarianceCanonical6 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance c2CovarianceCanonical7 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ)

local instance c2CovarianceCanonical8 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
     (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

local instance c2CovarianceCanonical9 : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup

local instance c2CovarianceCanonical10 : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace

local instance c2CovarianceCanonical11 : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup

local instance c2CovarianceCanonical12 : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace

local instance c2CovarianceCanonical13 : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid

/-- Full bilinear covariance of the actual differential on a symmetric C2 germ. -/
theorem differential_covariance :
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
(anchor₁ anchor₂ : M) (q : Poincare.DeTurckPrincipalSecondJet.E → Poincare.DeTurckPrincipalSecondJet.Bilin) (z : Poincare.DeTurckPrincipalSecondJet.E),
z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₁).target →
(extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₁).symm z ∈ (extChartAt (Poincare.closedSmoothModelWithCorners 3) anchor₂).source →
Filter.Eventually (fun y => Poincare.GeodesicTransport.cutoff (n := 3) anchor₁ y = 1) (nhds z) →
Filter.Eventually (fun y => Poincare.GeodesicTransport.cutoff (n := 3) anchor₂ y = 1)
 (nhds (Poincare.GeodesicTransport.chartTransition anchor₁ anchor₂ z)) →
ContDiffAt ℝ 2 q (Poincare.GeodesicTransport.chartTransition anchor₁ anchor₂ z) →
Filter.Eventually (fun y => ∀ v w : Poincare.DeTurckPrincipalSecondJet.E, q y v w = q y w v)
 (nhds (Poincare.GeodesicTransport.chartTransition anchor₁ anchor₂ z)) →
let DQ := fun (anchor : M) (r : Poincare.DeTurckPrincipalSecondJet.E → Poincare.DeTurckPrincipalSecondJet.Bilin) (y : Poincare.DeTurckPrincipalSecondJet.E) =>
 let G0 := _root_.CovariantDerivative.chartMetric (I := Poincare.closedSmoothModelWithCorners 3) g0.inner anchor
 let B := Poincare.GeodesicTransport.chartChristoffelField bg anchor
 Poincare.DeTurckJetLinearization.differential (B y) (fderiv ℝ B y)
  (G0 y) (fderiv ℝ G0 y) (fderiv ℝ (fderiv ℝ G0) y)
  ((r y, fderiv ℝ r y), fderiv ℝ (fderiv ℝ r) y)
let phi := Poincare.GeodesicTransport.chartTransition anchor₁ anchor₂
let Tq := fun y => Poincare.pullbackBilinearForm (q (phi y)) (fderiv ℝ phi y)
Poincare.pullbackBilinearForm (DQ anchor₂ q (phi z)) (fderiv ℝ phi z) =
 DQ anchor₁ Tq z := by
  intro M _ _ _ _ g0 bg anchor₁ anchor₂ q z hz hy hcut₁ hcut₂ hq hsymm
  dsimp only
  let phi : E → E := GeodesicTransport.chartTransition anchor₁ anchor₂
  let T := fun (r : E → Bilin) (y : E) =>
    pullbackBilinearForm (r (phi y)) (fderiv ℝ phi y)
  let DQ := fun (anchor : M) (r : E → Bilin) (y : E) =>
    let G0 := CovariantDerivative.chartMetric
      (I := closedSmoothModelWithCorners 3) g0.inner anchor
    let B := GeodesicTransport.chartChristoffelField bg anchor
    DeTurckJetLinearization.differential
      (B y) (fderiv ℝ B y) (G0 y) (fderiv ℝ G0 y)
      (fderiv ℝ (fderiv ℝ G0) y)
      ((r y, fderiv ℝ r y), fderiv ℝ (fderiv ℝ r) y)
  change pullbackBilinearForm (DQ anchor₂ q (phi z)) (fderiv ℝ phi z) =
    DQ anchor₁ (T q) z
  have hz₂ : phi z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor₂).target :=
    (extChartAt (closedSmoothModelWithCorners 3) anchor₂).map_source hy
  obtain ⟨η, _hη, _hcη, _hηU, _hone, hF, hcF, hFU, hFs, hF0, hF1, hF2⟩ :=
    DeTurckJetRealization.exists_compact_symmetric_realization q (phi z)
      (extChartAt (closedSmoothModelWithCorners 3) anchor₂).target
      (isOpen_extChartAt_target anchor₂) hz₂ hq hsymm
  let F := DeTurckJetRealization.realized η q (phi z)
  let H := DeTurckChartLift.chartLift anchor₂ F
  let F₁ := CovariantDerivative.chartMetric
    (I := closedSmoothModelWithCorners 3) H anchor₁
  let F₂ := CovariantDerivative.chartMetric
    (I := closedSmoothModelWithCorners 3) H anchor₂
  have hF₂ : F₂ =ᶠ[nhds (phi z)] F := by
    filter_upwards [(isOpen_extChartAt_target anchor₂).mem_nhds hz₂] with y hy₂
    exact DeTurckChartLift.chartMetric_chartLift anchor₂ F y hy₂
  have hjet₂ : ((F₂ (phi z), fderiv ℝ F₂ (phi z)),
      fderiv ℝ (fderiv ℝ F₂) (phi z)) =
      ((q (phi z), fderiv ℝ q (phi z)), fderiv ℝ (fderiv ℝ q) (phi z)) :=
    Prod.ext (Prod.ext (hF₂.eq_of_nhds.trans hF0) (hF₂.fderiv_eq.trans hF1))
      (hF₂.fderiv.fderiv_eq.trans hF2)
  obtain ⟨hphi, _htransport, hjet₁F⟩ :=
    DeTurckChartLiftOverlapJets.chartLift_overlap_twoJet M anchor₁ anchor₂ F z hz hy
  obtain ⟨hT0, hT1, hT2⟩ :=
    DeTurckPullbackTwoJet.pullback_twoJet_congr E q F phi z hq
      (hF.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      hphi hF0.symm hF1.symm hF2.symm
  have hjetT : ((T q z, fderiv ℝ (T q) z), fderiv ℝ (fderiv ℝ (T q)) z) =
      ((T F z, fderiv ℝ (T F) z), fderiv ℝ (fderiv ℝ (T F)) z) :=
    Prod.ext (Prod.ext hT0 hT1) hT2
  have hjet₁ : ((F₁ z, fderiv ℝ F₁ z), fderiv ℝ (fderiv ℝ F₁) z) =
      ((T q z, fderiv ℝ (T q) z), fderiv ℝ (fderiv ℝ (T q)) z) :=
    hjet₁F.trans hjetT.symm
  have hcov := DeTurckConstructedCovariance.chartLift_differential_covariance
    M g0 bg anchor₂ F hF hcF hFU hFs anchor₁ anchor₂ z hz hy hcut₁ hcut₂
  change pullbackBilinearForm (DQ anchor₂ F₂ (phi z)) (fderiv ℝ phi z) =
    DQ anchor₁ F₁ z at hcov
  have hDQ₂ : DQ anchor₂ F₂ (phi z) = DQ anchor₂ q (phi z) := by
    dsimp only [DQ]
    rw [hjet₂]
  have hDQ₁ : DQ anchor₁ F₁ z = DQ anchor₁ (T q) z := by
    dsimp only [DQ]
    rw [hjet₁]
  exact (congrArg (fun A : Bilin => pullbackBilinearForm A (fderiv ℝ phi z)) hDQ₂).symm.trans
    (hcov.trans hDQ₁)

end Poincare.DeTurckC2Covariance
