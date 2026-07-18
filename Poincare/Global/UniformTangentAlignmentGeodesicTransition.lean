import Poincare.Global.UniformAnchoredGeodesicTransition
import Poincare.Global.UniformTangentAlignmentFTransition
import Poincare.Global.UniformTangentAlignmentC2
import Poincare.Global.TangentAlignmentUniformCutoffRadius

/-!
# Fixed-anchor geodesic transition uniform over tangent alignments

The fixed-anchor raw F-transition, Cartan-map C2 package, and source/target
cutoff-one package now each provide a positive radius before the tangent
alignment is chosen.  Intersecting those three radii once yields the complete
geodesic-coefficient transition on one punctured normal ball for every
alignment at the fixed anchors.

This is the strongest fixed-anchor form needed by adaptive continuation: the
radius precedes `L`, while the selected differential fields may still depend
on `L`.  No anchor-varying compactness or `FieldProducer` premise is asserted.
-/

noncomputable section

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace UniformTangentAlignmentGeodesicTransition

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
For fixed source and target anchors, one positive punctured normal-coordinate
radius supports the complete diagonal signed Christoffel transition for every
tangent alignment.  The conclusion retains the C2, strict-derivative, and
cutoff germs required by the geodesic ODE and adaptive continuation consumers.
-/
theorem exists_uniform_cartanChartMap_chartChristoffelField_self_F_transition_law
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x0 p0,
        ∃ Afield Bfield : E → E ≃L[ℝ] E,
        ∃ DF : E → E →L[ℝ] E,
          (∀ v : E,
            DF v =
              CartanLocalIsometry.cartanChartDifferential
                L (Afield v) (Bfield v)) ∧
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
      UniformTangentAlignmentFTransition.exists_uniform_cartanChartMap_christoffelAt_F_transition_law_of_endpoint_hasFDerivAt_on_open
        (g := g) hcurv (x₀ := x0) (p₀ := p0) with
    ⟨rhoT, hrhoT, hrawAll⟩
  rcases
      UniformTangentAlignmentC2.exists_uniform_cartanChartMap_contDiffAt_two_on_punctured_ball
        (g := g) hcurv (x₀ := x0) (p₀ := p0) with
    ⟨rhoC, hrhoC, hC2All⟩
  rcases
      CartanMap.exists_uniform_source_target_cutoffOneLocus_preimage_ball
        g x0 p0 with
    ⟨rhoK, hrhoK, hcutAll⟩
  let rho : ℝ := min rhoT (min rhoC rhoK)
  have hrho : 0 < rho := by
    dsimp [rho]
    exact lt_min hrhoT (lt_min hrhoC hrhoK)
  refine ⟨rho, hrho, ?_⟩
  intro L
  rcases hrawAll L with
    ⟨Afield, Bfield, DF, hDF, hrawPackage⟩
  rcases hC2All L with
    ⟨_AC, _BC, _DFC, _hDFC, hC2⟩
  refine ⟨Afield, Bfield, DF, hDF, ?_⟩
  intro v hv hvne
  dsimp only
  have hvT : ‖v‖ < rhoT :=
    hv.trans_le (by dsimp [rho]; exact min_le_left _ _)
  have hvC : ‖v‖ < rhoC :=
    hv.trans_le (by
      dsimp [rho]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hvK : ‖v‖ < rhoK :=
    hv.trans_le (by
      dsimp [rho]
      exact (min_le_right _ _).trans (min_le_right _ _))
  rcases hC2 v hvC hvne with
    ⟨hvsrc, hLvsrc, heMchart, heSchart, _hsourceStrict, hF2⟩
  rcases hrawPackage v hvT hvne with
    ⟨hFstrict, hrawConsume⟩
  rcases hcutAll L v hvK with
    ⟨hcut0mem, hcut1mem⟩
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0
  let eS :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := roundSphereMetric3) p0
  let F := CartanDifferential.cartanChartMap g x0 p0 L
  have hFz : F (eM v) = eS (L v) := by
    change eS (L (eM.symm (eM v))) = eS (L v)
    rw [eM.left_inv hvsrc]
  have hcut0 : ∀ᶠ q in nhds (eM v),
      GeodesicTransport.cutoff (n := 3) x0 q = 1 :=
    IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
      hcut0mem
  have hcut1eS : ∀ᶠ q in nhds (eS (L v)),
      GeodesicTransport.cutoff (n := 3) p0 q = 1 :=
    IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
      hcut1mem
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

end UniformTangentAlignmentGeodesicTransition
end Poincare
