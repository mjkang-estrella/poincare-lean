import Poincare.Global.FTransitionGeodesicMap
import Poincare.Global.IsometryInstantiate

/-!
# Curvature-only Cartan transition in geodesic coefficients

This module converts the raw metric `christoffelAt` transition produced by
`FTransitionDone` into the actual `chartChristoffelField` transition used by
the chart geodesic ODE.  The radius is simultaneously shrunk into the source
and target cutoff-one loci, and the strict derivative already present in the
producer identifies its selected `DF` with the canonical `fderiv`.
-/

noncomputable section

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UniformAnchoredGeodesicTransition

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- A curvature-one Cartan chart map satisfies the diagonal signed
Christoffel transition for the actual source and target chart geodesic fields
throughout a common punctured normal ball.  The same package retains the
strict derivative and cutoff-one germs needed by the ODE consumer. -/
theorem exists_cartanChartMap_chartChristoffelField_self_F_transition_law
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) (L : CartanMap.TangentAlignment g x0 p0) :
    ∃ rho > (0 : ℝ),
      ∃ Afield Bfield : E → E ≃L[ℝ] E,
      ∃ DF : E → E →L[ℝ] E,
        (∀ v : E,
          DF v =
            CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)) ∧
        ∀ v : E, ‖v‖ < rho → v ≠ 0 →
          let eM :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0
          let eS :=
            GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p0
          let F := CartanDifferential.cartanChartMap g x0 p0 L
          v ∈ eM.source ∧
            L v ∈ eS.source ∧
            ContDiffAt ℝ 2 F (eM v) ∧
            HasStrictFDerivAt F (DF v) (eM v) ∧
            (∀ᶠ q in nhds (eM v),
              GeodesicTransport.cutoff (n := 3) x0 q = 1) ∧
            (∀ᶠ q in nhds (F (eM v)),
              GeodesicTransport.cutoff (n := 3) p0 q = 1) ∧
            ∀ w : E,
              GeodesicTransport.chartChristoffelField
                  roundSphereMetric3 p0 (F (eM v))
                  ((fderiv ℝ F (eM v)) w)
                  ((fderiv ℝ F (eM v)) w) =
                (fderiv ℝ F (eM v))
                    (GeodesicTransport.chartChristoffelField
                      g x0 (eM v) w w) -
                  ((fderiv ℝ (fun q : E => fderiv ℝ F q) (eM v)) w) w := by
  rcases
      FTransitionDone.exists_cartanChartMap_christoffelAt_F_transition_law_of_endpoint_hasFDerivAt_on_open
        (g := g) hcurv (x₀ := x0) (p₀ := p0) L with
    ⟨rhoT, hrhoT, Afield, Bfield, DF, hDF, hrawPackage⟩
  rcases
      UniformAnchoredFTransition.exists_cartanChartMap_contDiffAt_two_on_punctured_ball
        (g := g) hcurv (x₀ := x0) (p₀ := p0) L with
    ⟨rhoC, hrhoC, _AC, _BC, _DFC, _hDFC, hC2⟩
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p0
  have heM_cont : ContinuousAt (eM : E → E) 0 := by
    simpa [eM, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
      GeodesicTransport.expAt_chart_continuousAt_zero (g := g) (x₀ := x0)
  have heS_cont : ContinuousAt (eS : E → E) 0 := by
    simpa [eS, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
      GeodesicTransport.expAt_chart_continuousAt_zero
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p0)
  have heM0 : eM (0 : E) = extChartAt I x0 x0 := by
    simp [eM, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe,
      GeodesicTransport.expAt_zero]
  have heS0 : eS (0 : E) = extChartAt I p0 p0 := by
    simp [eS, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe,
      GeodesicTransport.expAt_zero]
  have hsource_preimage :
      eM ⁻¹' IsometryInstantiate.cutoffOneLocus x0 ∈ nhds (0 : E) := by
    apply heM_cont.preimage_mem_nhds
    rw [heM0]
    exact IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor (x₀ := x0)
  have htarget_cont : ContinuousAt (fun v : E => eS (L v)) 0 := by
    have hLcont : ContinuousAt (fun v : E => L v) 0 := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        L.toContinuousLinearEquiv.continuous.continuousAt
    simpa [Function.comp_def] using
      heS_cont.comp_of_eq hLcont (by simp)
  have htarget0 : eS (L (0 : E)) = extChartAt I p0 p0 := by
    simpa using heS0
  have htarget_preimage :
      (fun v : E => eS (L v)) ⁻¹'
          IsometryInstantiate.cutoffOneLocus p0 ∈ nhds (0 : E) := by
    apply htarget_cont.preimage_mem_nhds
    rw [htarget0]
    exact IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor (x₀ := p0)
  rcases Metric.mem_nhds_iff.mp hsource_preimage with
    ⟨rS, hrS, hrSsub⟩
  rcases Metric.mem_nhds_iff.mp htarget_preimage with
    ⟨rT, hrT, hrTsub⟩
  let rho : ℝ := min rhoT (min rhoC (min rS rT))
  have hrho : 0 < rho := by
    dsimp [rho]
    exact lt_min hrhoT (lt_min hrhoC (lt_min hrS hrT))
  refine ⟨rho, hrho, Afield, Bfield, DF, hDF, ?_⟩
  intro v hv hvne
  dsimp only
  have hvT : ‖v‖ < rhoT :=
    hv.trans_le (by dsimp [rho]; exact min_le_left _ _)
  have hvC : ‖v‖ < rhoC :=
    hv.trans_le (by
      dsimp [rho]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hvrS : ‖v‖ < rS :=
    hv.trans_le (by
      dsimp [rho]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hvrT : ‖v‖ < rT :=
    hv.trans_le (by
      dsimp [rho]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  rcases hC2 v hvC hvne with
    ⟨hvsrc, hLvsrc, heMchart, heSchart, _hsourceStrict, hF2⟩
  rcases hrawPackage v hvT hvne with ⟨hFstrict, hrawConsume⟩
  let F := CartanDifferential.cartanChartMap g x0 p0 L
  have hFz : F (eM v) = eS (L v) := by
    change eS (L (eM.symm (eM v))) = eS (L v)
    rw [eM.left_inv hvsrc]
  have hvballS : v ∈ ball (0 : E) rS := by
    simpa [mem_ball, dist_eq_norm] using hvrS
  have hvballT : v ∈ ball (0 : E) rT := by
    simpa [mem_ball, dist_eq_norm] using hvrT
  have hcut0 : ∀ᶠ q in nhds (eM v),
      GeodesicTransport.cutoff (n := 3) x0 q = 1 :=
    IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
      (hrSsub hvballS)
  have hcut1eS : ∀ᶠ q in nhds (eS (L v)),
      GeodesicTransport.cutoff (n := 3) p0 q = 1 :=
    IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
      (hrTsub hvballT)
  have hcut1 : ∀ᶠ q in nhds (F (eM v)),
      GeodesicTransport.cutoff (n := 3) p0 q = 1 := by
    rwa [hFz]
  let G0 : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric g.inner x0 z
  let G1 : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p0 z
  have hG0 : HasFDerivAt G0 (fderiv ℝ G0 (eM v)) (eM v) := by
    simpa [G0, eM] using
      UniformAnchoredFTransition.chartMetric_hasFDerivAt_of_mem_target
        g x0 heMchart
  have hG1 : HasFDerivAt G1 (fderiv ℝ G1 (F (eM v))) (F (eM v)) := by
    have hFchart : F (eM v) ∈ (extChartAt I p0).target := by
      rw [hFz]
      exact heSchart
    simpa [G1] using
      UniformAnchoredFTransition.chartMetric_hasFDerivAt_of_mem_target
        (M := RoundSphere3) roundSphereMetric3 p0 hFchart
  let b0 : LinearMap.BilinForm ℝ E :=
    UniformAnchoredFTransition.chartMetricBilin (G0 (eM v))
  let b1 : LinearMap.BilinForm ℝ E :=
    UniformAnchoredFTransition.chartMetricBilin (G1 (F (eM v)))
  have hb0 : b0.Nondegenerate := by
    simpa [b0, G0, eM] using
      UniformAnchoredFTransition.chartMetricBilin_nondegenerate_of_mem_target
        g x0 heMchart
  have hb1 : b1.Nondegenerate := by
    have hFchart : F (eM v) ∈ (extChartAt I p0).target := by
      rw [hFz]
      exact heSchart
    simpa [b1, G1] using
      UniformAnchoredFTransition.chartMetricBilin_nondegenerate_of_mem_target
        (M := RoundSphere3) roundSphereMetric3 p0 hFchart
  have hb0G : ∀ a b : E, b0 a b = G0 (eM v) a b := by
    intro a b
    rfl
  have hb1G : ∀ a b : E, b1 a b = G1 (F (eM v)) a b := by
    intro a b
    rfl
  have hendpoint :
      HasFDerivAt (fun q : E => fderiv ℝ F q)
        (fderiv ℝ (fun q : E => fderiv ℝ F q) (eM v)) (eM v) := by
    exact
      ((hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasFDerivAt
  have hDFf : DF v = fderiv ℝ F (eM v) := by
    simpa [F] using hFstrict.hasFDerivAt.fderiv.symm
  refine ⟨hvsrc, hLvsrc, ?_, ?_, hcut0, hcut1, ?_⟩
  · simpa [F, eM] using hF2
  · simpa [F, eM] using hFstrict
  intro w
  have hraw :=
    hrawConsume hvsrc
      (fun q : E => fderiv ℝ F q)
      (fderiv ℝ (fun q : E => fderiv ℝ F q) (eM v))
      Set.univ isOpen_univ (Set.mem_univ (eM v))
      (by intro q _hq; rfl) hendpoint
      (by simpa [F, eM] using hF2) hG0 hG1
      b0 b1 hb0 hb1 hb0G hb1G w w
  exact
    FTransitionGeodesicMap.chartChristoffelField_self_F_transition_of_christoffelAt
      (g := g) (x0 := x0) (p0 := p0) (F := F) (z := eM v)
      (D := DF v) hDFf hcut0 hcut1 b0 b1 hb0 hb1 hb0G hb1G w
      (by simpa [G0, G1] using hraw)

end UniformAnchoredGeodesicTransition
end Poincare
